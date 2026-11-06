import NetHack.Soko22Hazard87.AndIntroBlocks0023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro6000 (p : Pattern) (ha : d1646 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1620 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1621 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1645 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1646 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6001 (p : Pattern) (ha : d1653 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1610 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1611, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1615 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1616 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1651 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1652 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1653 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro6002 (p : Pattern) (ha : d1656 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1620 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1654 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1655 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1656 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6003 (p : Pattern) (ha : d1682 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1677 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1678 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1678, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1610 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1611 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1679 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1680 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1681 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d1682 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1682, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1682, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro6004 (p : Pattern) (ha : d62624 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5999 q ha hb
    | true =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6000 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6001 q ha hb
    | true =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6002 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6003 q ha hb
    | true =>
      simp only [d1683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5995 q ha hb
  have h9 (q : Pattern) (ha : d4525 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1797 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5995 q ha hb
    | true =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1798 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4526 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51764 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51765 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62624 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62624, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62624, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro6005 (p : Pattern) (ha : d62630 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2595 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5997 q ha hb
  have h2 (q : Pattern) (ha : d2596 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3590 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62625 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6004 q ha hb
  have h5 (q : Pattern) (ha : d3594 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5997 q ha hb
    | true =>
      simp only [d3594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5998 q ha hb
  have h6 (q : Pattern) (ha : d62626 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62627 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62628 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62629 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62630 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro6006 (p : Pattern) (ha : d62636 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62631 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6005 q ha hb
  have h2 (q : Pattern) (ha : d62632 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62633 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62634 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62635 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62636 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6007 (p : Pattern) (ha : d2102 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2093 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2098 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2099 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2100 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2101 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d2102 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2102, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2102, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro6008 (p : Pattern) (ha : d2106 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2103 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2104 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d2105 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d2106 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6009 (p : Pattern) (ha : d2611 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6007 q ha hb
    | true =>
      simp only [d2107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6008 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2611 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2611, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro6010 (p : Pattern) (ha : d3613 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6008 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3613 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3613, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3613, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro6011 (p : Pattern) (ha : d2127 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2093 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2094 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2094, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2098 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2099 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2100 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2126 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2127 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2127, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2127, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro6012 (p : Pattern) (ha : d2129 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2103 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2104 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2128 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2129 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6013 (p : Pattern) (ha : d2136 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2093 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2094 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2094, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2098 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d2099 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2134 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2135 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2136 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2136, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2136, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro6014 (p : Pattern) (ha : d2139 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2097 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2098, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2103 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d2137 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2138 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2139 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6015 (p : Pattern) (ha : d2161 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2156 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2157 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2157, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d2093 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2094 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d2158 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2159 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2160 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d2161 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2161, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2161, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro6016 (p : Pattern) (ha : d62641 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6011 q ha hb
    | true =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6012 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6013 q ha hb
    | true =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6014 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6015 q ha hb
    | true =>
      simp only [d2162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6007 q ha hb
  have h9 (q : Pattern) (ha : d4566 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2275 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6007 q ha hb
    | true =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2276 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4567 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51793 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51794 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62641 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62641, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62641, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro6017 (p : Pattern) (ha : d62647 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2612 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6009 q ha hb
  have h2 (q : Pattern) (ha : d2613 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3610 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62642 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6016 q ha hb
  have h5 (q : Pattern) (ha : d3614 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6009 q ha hb
    | true =>
      simp only [d3614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6010 q ha hb
  have h6 (q : Pattern) (ha : d62643 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62644 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62645 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62646 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62647 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro6018 (p : Pattern) (ha : d62653 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62648 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6017 q ha hb
  have h2 (q : Pattern) (ha : d62649 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62650 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62651 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62652 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62653 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6019 (p : Pattern) (ha : d62659 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62592 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5958 q ha hb
    | true =>
      simp only [d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5970 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62606 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5982 q ha hb
  have h3 (q : Pattern) (ha : d62607 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62621 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5994 q ha hb
  have h5 (q : Pattern) (ha : d62622 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62623 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62637 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6006 q ha hb
  have h8 (q : Pattern) (ha : d62638 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62639 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62640 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62654 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6018 q ha hb
  have h12 (q : Pattern) (ha : d62655 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62656 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62657 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62658 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62659 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6020 (p : Pattern) (ha : d62665 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62660 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6019 q ha hb
    | true =>
      simp only [d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62661 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62662 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62663 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62664 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62665 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6021 (p : Pattern) (ha : d62671 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62666 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6020 q ha hb
    | true =>
      simp only [d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62667 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62668 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62669 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62670 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62671 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6022 (p : Pattern) (ha : d62677 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62672 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6021 q ha hb
    | true =>
      simp only [d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62673 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62674 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62675 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62676 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62677 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6023 (p : Pattern) (ha : d62683 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62678 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6022 q ha hb
    | true =>
      simp only [d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62679 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62680 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62681 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62682 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62683 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6024 (p : Pattern) (ha : d62689 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62684 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6023 q ha hb
    | true =>
      simp only [d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62685 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62686 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62687 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62688 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62689 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6025 (p : Pattern) (ha : d62695 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62690 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6024 q ha hb
    | true =>
      simp only [d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62691 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62692 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62693 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62694 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62695 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6026 (p : Pattern) (ha : d62701 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62696 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6025 q ha hb
    | true =>
      simp only [d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62697 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62698 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62699 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62700 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62701 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6027 (p : Pattern) (ha : d62704 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2525 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5946 q ha hb
  have h2 (q : Pattern) (ha : d2526 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2527 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62702 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62703 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62704 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6028 (p : Pattern) (ha : d62712 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2537 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5952 q ha hb
  have h2 (q : Pattern) (ha : d2538 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2539 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62710 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62711 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62712 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6029 (p : Pattern) (ha : d62718 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62705 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6027 q ha hb
  have h2 (q : Pattern) (ha : d62706 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62707 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62708 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62709 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62713 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6028 q ha hb
  have h7 (q : Pattern) (ha : d62714 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62715 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62716 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62717 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62718 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6030 (p : Pattern) (ha : d62721 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2550 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5961 q ha hb
  have h2 (q : Pattern) (ha : d2551 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2552 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62719 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62720 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62721 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6031 (p : Pattern) (ha : d62727 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62722 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6030 q ha hb
  have h2 (q : Pattern) (ha : d62723 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62724 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62725 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62726 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62727 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6032 (p : Pattern) (ha : d62731 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2564 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5973 q ha hb
  have h2 (q : Pattern) (ha : d2565 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2566 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62729 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62730 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62731 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6033 (p : Pattern) (ha : d62737 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62732 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6032 q ha hb
  have h2 (q : Pattern) (ha : d62733 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62734 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62735 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62736 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62737 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6034 (p : Pattern) (ha : d62742 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2579 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5985 q ha hb
  have h2 (q : Pattern) (ha : d2580 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2581 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62740 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62741 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62742 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6035 (p : Pattern) (ha : d62748 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62743 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6034 q ha hb
  have h2 (q : Pattern) (ha : d62744 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62745 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62746 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62747 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62748 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6036 (p : Pattern) (ha : d62754 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2595 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5997 q ha hb
  have h2 (q : Pattern) (ha : d2596 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2597 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62752 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62753 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62754 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6037 (p : Pattern) (ha : d62760 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62755 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6036 q ha hb
  have h2 (q : Pattern) (ha : d62756 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62757 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62758 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62759 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62760 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6038 (p : Pattern) (ha : d62767 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2612 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6009 q ha hb
  have h2 (q : Pattern) (ha : d2613 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2614 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62765 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62766 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62767 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6039 (p : Pattern) (ha : d62773 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62768 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6038 q ha hb
  have h2 (q : Pattern) (ha : d62769 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62770 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62771 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62772 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62773 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6040 (p : Pattern) (ha : d62779 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62728 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6029 q ha hb
    | true =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6031 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62738 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6033 q ha hb
  have h3 (q : Pattern) (ha : d62739 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62749 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6035 q ha hb
  have h5 (q : Pattern) (ha : d62750 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62751 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62761 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6037 q ha hb
  have h8 (q : Pattern) (ha : d62762 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62763 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62764 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62774 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6039 q ha hb
  have h12 (q : Pattern) (ha : d62775 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62776 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62777 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62778 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62779 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6041 (p : Pattern) (ha : d62785 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62780 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6040 q ha hb
    | true =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62781 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62782 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62783 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62784 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62785 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6042 (p : Pattern) (ha : d62791 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62786 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6041 q ha hb
    | true =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62787 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62788 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62789 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62790 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62791 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6043 (p : Pattern) (ha : d62797 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62792 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6042 q ha hb
    | true =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62793 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62794 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62795 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62796 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62797 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6044 (p : Pattern) (ha : d62803 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62798 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6043 q ha hb
    | true =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62799 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62800 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62801 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62802 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62803 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6045 (p : Pattern) (ha : d62809 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62804 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6044 q ha hb
    | true =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62805 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62806 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62807 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62808 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62809 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6046 (p : Pattern) (ha : d62815 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62810 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6045 q ha hb
    | true =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62811 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62812 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62813 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62814 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62815 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6047 (p : Pattern) (ha : d62821 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62816 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6046 q ha hb
    | true =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62817 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62818 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62819 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62820 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62821 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6048 (p : Pattern) (ha : d3503 p = 1) (hb : d62374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3497 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3498 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3498, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3498, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d3499 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3500 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3501 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3502 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d3503 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro6049 (p : Pattern) (ha : d62374 p = 1) (hb : d62560 p = 1) : d59645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d213 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2525 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3508 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d62554 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62374, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62374, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d214 q = 1) (hb : d62374 q = 1) : d214 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d62374 q = 1) (hb : d62556 q = 1) : d59641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62556, d59641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62556, d59641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d62374 q = 1) (hb : d62557 q = 1) : d59642 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62557, d59642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62557, d59642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62558 q = 1) : d59643 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62558, d59643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62558, d59643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62559 q = 1) : d59644 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62559, d59644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d62559, d59644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62560 q = 1) : d59645 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62560, d59645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d62560, d59645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro6050 (p : Pattern) (ha : d62374 p = 1) (hb : d62572 p = 1) : d73366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2536 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2537 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3521 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d62566 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62374, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62374, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2536 q = 1) (hb : d54978 q = 1) : d2536 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d213 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d3524 q = 1) (hb : d62374 q = 1) : d73361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3524, d62374, d73361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3524, d62374, d73361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62568 q = 1) : d73362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62568, d73362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62568, d73362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62569 q = 1) : d73363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62569, d73363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d62569, d73363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62570 q = 1) : d73364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62570, d73364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62570, d73364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62571 q = 1) : d73365 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62571, d73365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d62571, d73365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62572 q = 1) : d73366 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62572, d73366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62572, d73366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro6051 (p : Pattern) (ha : d62374 p = 1) (hb : d62578 p = 1) : d73372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3504 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6048 q ha hb
  have h2 (q : Pattern) (ha : d3505 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3506 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3507 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62561 q = 1) : d59646 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62561, d59646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62561, d59646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6049 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62562 q = 1) : d59647 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62562, d59647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62562, d59647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62563 q = 1) : d59648 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62563, d59648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62563, d59648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62564 q = 1) : d59649 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62564, d59649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62564, d59649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62374 q = 1) (hb : d62565 q = 1) : d59650 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62565, d59650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d62565, d59650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62374 q = 1) (hb : d62573 q = 1) : d73367 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62573, d73367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62573, d73367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6050 q ha hb
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62574 q = 1) : d73368 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62574, d73368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62574, d73368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62575 q = 1) : d73369 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62575, d73369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62575, d73369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62576 q = 1) : d73370 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62576, d73370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62576, d73370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62577 q = 1) : d73371 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62577, d73371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62577, d73371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62578 q = 1) : d73372 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62578, d73372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62578, d73372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6052 (p : Pattern) (ha : d62374 p = 1) (hb : d62585 p = 1) : d73378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2550 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3536 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d62579 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62374, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62374, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2549 q = 1) (hb : d54978 q = 1) : d2549 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d3539 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d3540 q = 1) (hb : d62374 q = 1) : d73373 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3540, d62374, d73373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3540, d62374, d73373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62581 q = 1) : d73374 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62581, d73374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62581, d73374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62582 q = 1) : d73375 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62582, d73375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d62582, d73375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62583 q = 1) : d73376 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62583, d73376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62583, d73376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62584 q = 1) : d73377 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62584, d73377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d62584, d73377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62585 q = 1) : d73378 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62585, d73378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62585, d73378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro6053 (p : Pattern) (ha : d62374 p = 1) (hb : d62591 p = 1) : d73384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62586 q = 1) : d73379 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62586, d73379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62586, d73379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6052 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62587 q = 1) : d73380 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62587, d73380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62587, d73380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62588 q = 1) : d73381 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62588, d73381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62588, d73381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62589 q = 1) : d73382 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62589, d73382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62589, d73382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62590 q = 1) : d73383 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62590, d73383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62590, d73383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62591 q = 1) : d73384 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62591, d73384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62591, d73384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6054 (p : Pattern) (ha : d62374 p = 1) (hb : d62599 p = 1) : d73391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2564 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3553 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d62593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62374, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62374, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2563 q = 1) (hb : d54978 q = 1) : d2563 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d3556 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d3557 q = 1) (hb : d62374 q = 1) : d73386 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3557, d62374, d73386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3557, d62374, d73386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62595 q = 1) : d73387 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62595, d73387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62595, d73387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62596 q = 1) : d73388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62596, d73388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d62596, d73388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62597 q = 1) : d73389 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62597, d73389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62597, d73389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62598 q = 1) : d73390 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62598, d73390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d62598, d73390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62599 q = 1) : d73391 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62599, d73391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62599, d73391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro6055 (p : Pattern) (ha : d62374 p = 1) (hb : d62605 p = 1) : d73397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62600 q = 1) : d73392 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62600, d73392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62600, d73392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6054 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62601 q = 1) : d73393 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62601, d73393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62601, d73393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62602 q = 1) : d73394 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62602, d73394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62602, d73394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62603 q = 1) : d73395 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62603, d73395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62603, d73395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62604 q = 1) : d73396 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62604, d73396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62604, d73396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62605 q = 1) : d73397 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62605, d73397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62605, d73397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6056 (p : Pattern) (ha : d62374 p = 1) (hb : d62614 p = 1) : d73405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2579 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3571 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d62608 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62374, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62374, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2578 q = 1) (hb : d54978 q = 1) : d2578 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d3574 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d3575 q = 1) (hb : d62374 q = 1) : d73400 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3575, d62374, d73400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3575, d62374, d73400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62610 q = 1) : d73401 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62610, d73401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62610, d73401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62611 q = 1) : d73402 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62611, d73402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d62611, d73402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62612 q = 1) : d73403 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62612, d73403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62612, d73403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62613 q = 1) : d73404 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62613, d73404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d62613, d73404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62614 q = 1) : d73405 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62614, d73405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62614, d73405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro6057 (p : Pattern) (ha : d62374 p = 1) (hb : d62620 p = 1) : d73411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62615 q = 1) : d73406 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62615, d73406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62615, d73406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6056 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62616 q = 1) : d73407 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62616, d73407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62616, d73407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62617 q = 1) : d73408 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62617, d73408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62617, d73408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62618 q = 1) : d73409 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62618, d73409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62618, d73409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62619 q = 1) : d73410 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62619, d73410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62619, d73410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62620 q = 1) : d73411 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62620, d73411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62620, d73411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6058 (p : Pattern) (ha : d62374 p = 1) (hb : d62630 p = 1) : d73420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2595 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3590 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d62624 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62374, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62374, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2594 q = 1) (hb : d54978 q = 1) : d2594 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d3593 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d3594 q = 1) (hb : d62374 q = 1) : d73415 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3594, d62374, d73415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3594, d62374, d73415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62626 q = 1) : d73416 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62626, d73416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62626, d73416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62627 q = 1) : d73417 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62627, d73417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d62627, d73417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62628 q = 1) : d73418 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62628, d73418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62628, d73418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62629 q = 1) : d73419 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62629, d73419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d62629, d73419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62630 q = 1) : d73420 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62630, d73420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62630, d73420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro6059 (p : Pattern) (ha : d62374 p = 1) (hb : d62636 p = 1) : d73426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62631 q = 1) : d73421 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62631, d73421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62631, d73421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6058 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62632 q = 1) : d73422 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62632, d73422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62632, d73422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62633 q = 1) : d73423 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62633, d73423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62633, d73423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62634 q = 1) : d73424 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62634, d73424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62634, d73424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62635 q = 1) : d73425 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62635, d73425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62635, d73425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62636 q = 1) : d73426 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62636, d73426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62636, d73426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6060 (p : Pattern) (ha : d62374 p = 1) (hb : d62647 p = 1) : d73436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2612 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3610 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d62641 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62374, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62374, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2611 q = 1) (hb : d54978 q = 1) : d2611 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d3613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d3614 q = 1) (hb : d62374 q = 1) : d73431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3614, d62374, d73431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3614, d62374, d73431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62643 q = 1) : d73432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62643, d73432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62643, d73432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62644 q = 1) : d73433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62644, d73433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d62644, d73433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62645 q = 1) : d73434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62645, d73434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d62645, d73434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62646 q = 1) : d73435 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62646, d73435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d62646, d73435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62647 q = 1) : d73436 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62647, d73436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62647, d73436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro6061 (p : Pattern) (ha : d62374 p = 1) (hb : d62653 p = 1) : d73442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62648 q = 1) : d73437 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62648, d73437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62648, d73437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6060 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62649 q = 1) : d73438 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62649, d73438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62649, d73438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62650 q = 1) : d73439 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62650, d73439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62650, d73439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62651 q = 1) : d73440 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62651, d73440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62651, d73440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62652 q = 1) : d73441 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62652, d73441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62652, d73441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62653 q = 1) : d73442 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62653, d73442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62653, d73442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6062 (p : Pattern) (ha : d62374 p = 1) (hb : d62659 p = 1) : d73448 p = 1 := by
  have h0 (q : Pattern) (ha : d62374 q = 1) (hb : d62592 q = 1) : d73385 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62592, d73385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6051 q ha hb
    | true =>
      simp only [d62592, d73385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6053 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62606 q = 1) : d73398 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62606, d73398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62606, d73398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6055 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62607 q = 1) : d73399 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62607, d73399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62607, d73399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62621 q = 1) : d73412 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62621, d73412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62621, d73412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6057 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62622 q = 1) : d73413 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62622, d73413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62622, d73413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62623 q = 1) : d73414 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62623, d73414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62623, d73414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62637 q = 1) : d73427 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62637, d73427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62637, d73427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6059 q ha hb
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62638 q = 1) : d73428 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62638, d73428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62638, d73428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62374 q = 1) (hb : d62639 q = 1) : d73429 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62639, d73429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62639, d73429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62374 q = 1) (hb : d62640 q = 1) : d73430 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62640, d73430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62640, d73430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62654 q = 1) : d73443 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62654, d73443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62654, d73443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6061 q ha hb
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62655 q = 1) : d73444 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62655, d73444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62655, d73444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62656 q = 1) : d73445 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62656, d73445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62656, d73445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62657 q = 1) : d73446 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62657, d73446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62657, d73446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62658 q = 1) : d73447 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62658, d73447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62658, d73447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62374 q = 1) (hb : d62659 q = 1) : d73448 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62659, d73448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62659, d73448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro6063 (p : Pattern) (ha : d62374 p = 1) (hb : d62665 p = 1) : d73454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62660 q = 1) : d73449 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62660, d73449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6062 q ha hb
    | true =>
      simp only [d62660, d73449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62661 q = 1) : d73450 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62661, d73450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62661, d73450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62662 q = 1) : d73451 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62662, d73451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62662, d73451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62663 q = 1) : d73452 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62663, d73452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62663, d73452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62664 q = 1) : d73453 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62664, d73453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62664, d73453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62665 q = 1) : d73454 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62665, d73454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62665, d73454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6064 (p : Pattern) (ha : d62374 p = 1) (hb : d62671 p = 1) : d73460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62666 q = 1) : d73455 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62666, d73455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6063 q ha hb
    | true =>
      simp only [d62666, d73455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62667 q = 1) : d73456 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62667, d73456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62667, d73456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62668 q = 1) : d73457 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62668, d73457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62668, d73457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62669 q = 1) : d73458 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62669, d73458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62669, d73458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62670 q = 1) : d73459 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62670, d73459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62670, d73459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62671 q = 1) : d73460 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62671, d73460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62671, d73460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6065 (p : Pattern) (ha : d62374 p = 1) (hb : d62677 p = 1) : d73466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62672 q = 1) : d73461 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62672, d73461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6064 q ha hb
    | true =>
      simp only [d62672, d73461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62673 q = 1) : d73462 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62673, d73462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62673, d73462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62674 q = 1) : d73463 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62674, d73463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62674, d73463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62675 q = 1) : d73464 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62675, d73464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62675, d73464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62676 q = 1) : d73465 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62676, d73465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62676, d73465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62677 q = 1) : d73466 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62677, d73466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62677, d73466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6066 (p : Pattern) (ha : d62374 p = 1) (hb : d62683 p = 1) : d73472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62678 q = 1) : d73467 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62678, d73467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6065 q ha hb
    | true =>
      simp only [d62678, d73467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62679 q = 1) : d73468 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62679, d73468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62679, d73468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62680 q = 1) : d73469 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62680, d73469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62680, d73469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62681 q = 1) : d73470 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62681, d73470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62681, d73470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62682 q = 1) : d73471 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62682, d73471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62682, d73471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62683 q = 1) : d73472 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62683, d73472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62683, d73472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6067 (p : Pattern) (ha : d62374 p = 1) (hb : d62689 p = 1) : d73478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62684 q = 1) : d73473 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62684, d73473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6066 q ha hb
    | true =>
      simp only [d62684, d73473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62685 q = 1) : d73474 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62685, d73474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62685, d73474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62686 q = 1) : d73475 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62686, d73475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62686, d73475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62687 q = 1) : d73476 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62687, d73476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62687, d73476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62688 q = 1) : d73477 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62688, d73477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62688, d73477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62689 q = 1) : d73478 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62689, d73478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62689, d73478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6068 (p : Pattern) (ha : d62374 p = 1) (hb : d62695 p = 1) : d73484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62690 q = 1) : d73479 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62690, d73479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6067 q ha hb
    | true =>
      simp only [d62690, d73479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62691 q = 1) : d73480 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62691, d73480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62691, d73480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62692 q = 1) : d73481 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62692, d73481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62692, d73481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62693 q = 1) : d73482 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62693, d73482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62693, d73482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62694 q = 1) : d73483 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62694, d73483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62694, d73483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62695 q = 1) : d73484 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62695, d73484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62695, d73484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6069 (p : Pattern) (ha : d62374 p = 1) (hb : d62701 p = 1) : d73490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62696 q = 1) : d73485 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62696, d73485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6068 q ha hb
    | true =>
      simp only [d62696, d73485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62697 q = 1) : d73486 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62697, d73486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62697, d73486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62698 q = 1) : d73487 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62698, d73487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62698, d73487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62699 q = 1) : d73488 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62699, d73488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62699, d73488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62700 q = 1) : d73489 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62700, d73489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62700, d73489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62701 q = 1) : d73490 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62701, d73490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62701, d73490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6070 (p : Pattern) (ha : d59645 p = 1) (hb : d61379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61373 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59641 q = 1) (hb : d61375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d59641, d61375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59641, d61375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59642 q = 1) (hb : d61376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59642, d61376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d59642, d61376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d59643 q = 1) (hb : d61377 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59643, d61377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59643, d61377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d59644 q = 1) (hb : d61378 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59644, d61378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d59644, d61378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d59645 q = 1) (hb : d61379 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59645, d61379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d59645, d61379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h8 p ha hb
theorem andIntro6071 (p : Pattern) (ha : d61394 p = 1) (hb : d73366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61389 q = 1) (hb : d73361 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61389, d73361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5739 q hb ha
    | true =>
      simp only [d61389, d73361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d61390 q = 1) (hb : d73362 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61390, d73362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61390, d73362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61391 q = 1) (hb : d73363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61391, d73363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61391, d73363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d61392 q = 1) (hb : d73364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61392, d73364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61392, d73364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61393 q = 1) (hb : d73365 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61393, d73365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61393, d73365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d61394 q = 1) (hb : d73366 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61394, d73366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61394, d73366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro6072 (p : Pattern) (ha : d61400 p = 1) (hb : d73372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61370 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d59646 q = 1) (hb : d61380 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59646, d61380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59646, d61380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6070 q ha hb
  have h3 (q : Pattern) (ha : d59647 q = 1) (hb : d61381 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59647, d61381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59647, d61381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d59648 q = 1) (hb : d61382 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59648, d61382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59648, d61382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d59649 q = 1) (hb : d61383 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59649, d61383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d59649, d61383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59650 q = 1) (hb : d61384 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59650, d61384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59650, d61384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61395 q = 1) (hb : d73367 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61395, d73367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61395, d73367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6071 q ha hb
  have h8 (q : Pattern) (ha : d61396 q = 1) (hb : d73368 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61396, d73368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61396, d73368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61397 q = 1) (hb : d73369 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61397, d73369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61397, d73369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61398 q = 1) (hb : d73370 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61398, d73370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61398, d73370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61399 q = 1) (hb : d73371 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61399, d73371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61399, d73371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d61400 q = 1) (hb : d73372 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61400, d73372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d61400, d73372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro6073 (p : Pattern) (ha : d61410 p = 1) (hb : d73378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61403 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61405 q = 1) (hb : d73373 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61405, d73373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5744 q hb ha
    | true =>
      simp only [d61405, d73373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d61406 q = 1) (hb : d73374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61406, d73374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61406, d73374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61407 q = 1) (hb : d73375 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61407, d73375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61407, d73375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d61408 q = 1) (hb : d73376 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61408, d73376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61408, d73376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61409 q = 1) (hb : d73377 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61409, d73377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61409, d73377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d61410 q = 1) (hb : d73378 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61410, d73378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61410, d73378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro6074 (p : Pattern) (ha : d61416 p = 1) (hb : d73384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61411 q = 1) (hb : d73379 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61411, d73379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61411, d73379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6073 q ha hb
  have h2 (q : Pattern) (ha : d61412 q = 1) (hb : d73380 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61412, d73380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61412, d73380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61413 q = 1) (hb : d73381 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61413, d73381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61413, d73381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61414 q = 1) (hb : d73382 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61414, d73382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61414, d73382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61415 q = 1) (hb : d73383 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61415, d73383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61415, d73383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61416 q = 1) (hb : d73384 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61416, d73384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61416, d73384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6075 (p : Pattern) (ha : d61427 p = 1) (hb : d73391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61420 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61422 q = 1) (hb : d73386 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61422, d73386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5750 q hb ha
    | true =>
      simp only [d61422, d73386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d61423 q = 1) (hb : d73387 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61423, d73387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61423, d73387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61424 q = 1) (hb : d73388 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61424, d73388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61424, d73388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d61425 q = 1) (hb : d73389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61425, d73389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61425, d73389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61426 q = 1) (hb : d73390 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61426, d73390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61426, d73390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d61427 q = 1) (hb : d73391 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61427, d73391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61427, d73391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro6076 (p : Pattern) (ha : d61433 p = 1) (hb : d73397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61428 q = 1) (hb : d73392 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61428, d73392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61428, d73392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6075 q ha hb
  have h2 (q : Pattern) (ha : d61429 q = 1) (hb : d73393 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61429, d73393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61429, d73393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61430 q = 1) (hb : d73394 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61430, d73394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61430, d73394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61431 q = 1) (hb : d73395 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61431, d73395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61431, d73395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61432 q = 1) (hb : d73396 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61432, d73396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61432, d73396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61433 q = 1) (hb : d73397 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61433, d73397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61433, d73397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6077 (p : Pattern) (ha : d61445 p = 1) (hb : d73405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61438 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61439 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61440 q = 1) (hb : d73400 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61440, d73400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5756 q hb ha
    | true =>
      simp only [d61440, d73400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d61441 q = 1) (hb : d73401 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61441, d73401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61441, d73401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61442 q = 1) (hb : d73402 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61442, d73402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61442, d73402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d61443 q = 1) (hb : d73403 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61443, d73403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61443, d73403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61444 q = 1) (hb : d73404 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61444, d73404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61444, d73404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d61445 q = 1) (hb : d73405 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61445, d73405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61445, d73405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro6078 (p : Pattern) (ha : d61451 p = 1) (hb : d73411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61446 q = 1) (hb : d73406 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61446, d73406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61446, d73406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6077 q ha hb
  have h2 (q : Pattern) (ha : d61447 q = 1) (hb : d73407 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61447, d73407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61447, d73407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61448 q = 1) (hb : d73408 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61448, d73408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61448, d73408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61449 q = 1) (hb : d73409 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61449, d73409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61449, d73409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61450 q = 1) (hb : d73410 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61450, d73410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61450, d73410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61451 q = 1) (hb : d73411 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61451, d73411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61451, d73411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6079 (p : Pattern) (ha : d61464 p = 1) (hb : d73420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61457 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61458 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61459 q = 1) (hb : d73415 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61459, d73415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5762 q hb ha
    | true =>
      simp only [d61459, d73415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d61460 q = 1) (hb : d73416 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61460, d73416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61460, d73416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61461 q = 1) (hb : d73417 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61461, d73417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61461, d73417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d61462 q = 1) (hb : d73418 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61462, d73418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61462, d73418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61463 q = 1) (hb : d73419 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61463, d73419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61463, d73419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d61464 q = 1) (hb : d73420 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61464, d73420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61464, d73420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro6080 (p : Pattern) (ha : d61470 p = 1) (hb : d73426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61465 q = 1) (hb : d73421 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61465, d73421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61465, d73421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6079 q ha hb
  have h2 (q : Pattern) (ha : d61466 q = 1) (hb : d73422 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61466, d73422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61466, d73422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61467 q = 1) (hb : d73423 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61467, d73423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61467, d73423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61468 q = 1) (hb : d73424 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61468, d73424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61468, d73424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61469 q = 1) (hb : d73425 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61469, d73425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61469, d73425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61470 q = 1) (hb : d73426 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61470, d73426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61470, d73426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6081 (p : Pattern) (ha : d61484 p = 1) (hb : d73436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61477 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61478 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d61479 q = 1) (hb : d73431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61479, d73431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5768 q hb ha
    | true =>
      simp only [d61479, d73431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d61480 q = 1) (hb : d73432 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61480, d73432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61480, d73432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61481 q = 1) (hb : d73433 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61481, d73433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61481, d73433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d61482 q = 1) (hb : d73434 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61482, d73434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61482, d73434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61483 q = 1) (hb : d73435 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61483, d73435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61483, d73435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d61484 q = 1) (hb : d73436 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61484, d73436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d61484, d73436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h8 p ha hb
theorem andIntro6082 (p : Pattern) (ha : d61490 p = 1) (hb : d73442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61485 q = 1) (hb : d73437 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61485, d73437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61485, d73437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6081 q ha hb
  have h2 (q : Pattern) (ha : d61486 q = 1) (hb : d73438 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61486, d73438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61486, d73438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61487 q = 1) (hb : d73439 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61487, d73439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61487, d73439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61488 q = 1) (hb : d73440 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61488, d73440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61488, d73440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61489 q = 1) (hb : d73441 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61489, d73441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61489, d73441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61490 q = 1) (hb : d73442 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61490, d73442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d61490, d73442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6083 (p : Pattern) (ha : d61496 p = 1) (hb : d73448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d61417 q = 1) (hb : d73385 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61417, d73385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6072 q ha hb
    | true =>
      simp only [d61417, d73385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6074 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d61434 q = 1) (hb : d73398 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61434, d73398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61434, d73398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6076 q ha hb
  have h3 (q : Pattern) (ha : d61435 q = 1) (hb : d73399 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61435, d73399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61435, d73399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61452 q = 1) (hb : d73412 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61452, d73412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61452, d73412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6078 q ha hb
  have h5 (q : Pattern) (ha : d61453 q = 1) (hb : d73413 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61453, d73413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61453, d73413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61454 q = 1) (hb : d73414 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61454, d73414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61454, d73414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d61471 q = 1) (hb : d73427 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61471, d73427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61471, d73427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6080 q ha hb
  have h8 (q : Pattern) (ha : d61472 q = 1) (hb : d73428 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61472, d73428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61472, d73428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61473 q = 1) (hb : d73429 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61473, d73429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61473, d73429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61474 q = 1) (hb : d73430 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61474, d73430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d61474, d73430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61491 q = 1) (hb : d73443 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61491, d73443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61491, d73443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6082 q ha hb
  have h12 (q : Pattern) (ha : d61492 q = 1) (hb : d73444 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61492, d73444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61492, d73444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d61493 q = 1) (hb : d73445 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61493, d73445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61493, d73445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d61494 q = 1) (hb : d73446 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61494, d73446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d61494, d73446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d61495 q = 1) (hb : d73447 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61495, d73447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d61495, d73447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d61496 q = 1) (hb : d73448 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61496, d73448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d61496, d73448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro6084 (p : Pattern) (ha : d61502 p = 1) (hb : d73454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61497 q = 1) (hb : d73449 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61497, d73449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6083 q ha hb
    | true =>
      simp only [d61497, d73449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61498 q = 1) (hb : d73450 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61498, d73450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61498, d73450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61499 q = 1) (hb : d73451 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61499, d73451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61499, d73451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61500 q = 1) (hb : d73452 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61500, d73452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61500, d73452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61501 q = 1) (hb : d73453 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61501, d73453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61501, d73453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61502 q = 1) (hb : d73454 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61502, d73454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61502, d73454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6085 (p : Pattern) (ha : d61508 p = 1) (hb : d73460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61503 q = 1) (hb : d73455 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61503, d73455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6084 q ha hb
    | true =>
      simp only [d61503, d73455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61504 q = 1) (hb : d73456 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61504, d73456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61504, d73456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61505 q = 1) (hb : d73457 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61505, d73457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61505, d73457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61506 q = 1) (hb : d73458 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61506, d73458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61506, d73458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61507 q = 1) (hb : d73459 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61507, d73459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61507, d73459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61508 q = 1) (hb : d73460 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61508, d73460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61508, d73460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6086 (p : Pattern) (ha : d61514 p = 1) (hb : d73466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61509 q = 1) (hb : d73461 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61509, d73461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6085 q ha hb
    | true =>
      simp only [d61509, d73461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61510 q = 1) (hb : d73462 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61510, d73462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61510, d73462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61511 q = 1) (hb : d73463 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61511, d73463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61511, d73463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61512 q = 1) (hb : d73464 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61512, d73464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61512, d73464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61513 q = 1) (hb : d73465 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61513, d73465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61513, d73465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61514 q = 1) (hb : d73466 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61514, d73466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61514, d73466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6087 (p : Pattern) (ha : d61520 p = 1) (hb : d73472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61515 q = 1) (hb : d73467 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61515, d73467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6086 q ha hb
    | true =>
      simp only [d61515, d73467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61516 q = 1) (hb : d73468 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61516, d73468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61516, d73468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61517 q = 1) (hb : d73469 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61517, d73469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61517, d73469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61518 q = 1) (hb : d73470 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61518, d73470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61518, d73470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61519 q = 1) (hb : d73471 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61519, d73471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61519, d73471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61520 q = 1) (hb : d73472 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61520, d73472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61520, d73472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6088 (p : Pattern) (ha : d61526 p = 1) (hb : d73478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61521 q = 1) (hb : d73473 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61521, d73473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6087 q ha hb
    | true =>
      simp only [d61521, d73473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61522 q = 1) (hb : d73474 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61522, d73474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61522, d73474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61523 q = 1) (hb : d73475 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61523, d73475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61523, d73475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61524 q = 1) (hb : d73476 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61524, d73476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61524, d73476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61525 q = 1) (hb : d73477 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61525, d73477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61525, d73477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61526 q = 1) (hb : d73478 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61526, d73478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61526, d73478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6089 (p : Pattern) (ha : d61532 p = 1) (hb : d73484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61527 q = 1) (hb : d73479 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61527, d73479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6088 q ha hb
    | true =>
      simp only [d61527, d73479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61528 q = 1) (hb : d73480 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61528, d73480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61528, d73480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61529 q = 1) (hb : d73481 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61529, d73481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61529, d73481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61530 q = 1) (hb : d73482 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61530, d73482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61530, d73482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61531 q = 1) (hb : d73483 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61531, d73483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61531, d73483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61532 q = 1) (hb : d73484 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61532, d73484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61532, d73484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6090 (p : Pattern) (ha : d61538 p = 1) (hb : d73490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61533 q = 1) (hb : d73485 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61533, d73485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6089 q ha hb
    | true =>
      simp only [d61533, d73485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d61534 q = 1) (hb : d73486 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61534, d73486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61534, d73486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d61535 q = 1) (hb : d73487 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61535, d73487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61535, d73487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d61536 q = 1) (hb : d73488 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61536, d73488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61536, d73488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d61537 q = 1) (hb : d73489 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61537, d73489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61537, d73489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d61538 q = 1) (hb : d73490 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61538, d73490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61538, d73490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6091 (p : Pattern) (ha : d62374 p = 1) (hb : d62704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d213 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2525 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2527 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro6092 (p : Pattern) (ha : d62374 p = 1) (hb : d62712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2536 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2537 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2539 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro6093 (p : Pattern) (ha : d62374 p = 1) (hb : d62718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6091 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6092 q ha hb
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62374 q = 1) (hb : d62716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62374 q = 1) (hb : d62717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6094 (p : Pattern) (ha : d62374 p = 1) (hb : d62721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2550 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2552 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62719 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62720 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62721 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro6095 (p : Pattern) (ha : d62374 p = 1) (hb : d62727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62722 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6094 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62723 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62725 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62726 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62727 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6096 (p : Pattern) (ha : d62374 p = 1) (hb : d62731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2564 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2566 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62731 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro6097 (p : Pattern) (ha : d62374 p = 1) (hb : d62737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62732 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6096 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62733 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62734 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62735 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62736 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62737 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6098 (p : Pattern) (ha : d62374 p = 1) (hb : d62742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2579 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2581 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro6099 (p : Pattern) (ha : d62374 p = 1) (hb : d62748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6098 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6100 (p : Pattern) (ha : d62374 p = 1) (hb : d62754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2595 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2597 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro6101 (p : Pattern) (ha : d62374 p = 1) (hb : d62760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6100 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6102 (p : Pattern) (ha : d62374 p = 1) (hb : d62767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2612 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d62374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2614 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62765 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62766 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62767 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro6103 (p : Pattern) (ha : d62374 p = 1) (hb : d62773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62768 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6102 q ha hb
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62769 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62770 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62771 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62772 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62773 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6104 (p : Pattern) (ha : d62374 p = 1) (hb : d62779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62374 q = 1) (hb : d62728 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6093 q ha hb
    | true =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6095 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62738 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6097 q ha hb
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62739 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6099 q ha hb
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62374 q = 1) (hb : d62761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6101 q ha hb
  have h8 (q : Pattern) (ha : d62374 q = 1) (hb : d62762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62374 q = 1) (hb : d62763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62374 q = 1) (hb : d62764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62374 q = 1) (hb : d62774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6103 q ha hb
  have h12 (q : Pattern) (ha : d62374 q = 1) (hb : d62775 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62374 q = 1) (hb : d62776 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62374 q = 1) (hb : d62777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62374 q = 1) (hb : d62778 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62374 q = 1) (hb : d62779 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro6105 (p : Pattern) (ha : d62374 p = 1) (hb : d62785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62780 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6104 q ha hb
    | true =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62781 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62782 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62783 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62784 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62785 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6106 (p : Pattern) (ha : d62374 p = 1) (hb : d62791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62786 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6105 q ha hb
    | true =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62787 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62788 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62789 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62790 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62791 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6107 (p : Pattern) (ha : d62374 p = 1) (hb : d62797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62792 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6106 q ha hb
    | true =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62793 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62794 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62795 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62796 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62797 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6108 (p : Pattern) (ha : d62374 p = 1) (hb : d62803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62798 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6107 q ha hb
    | true =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62799 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62800 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62801 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62802 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62803 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6109 (p : Pattern) (ha : d62374 p = 1) (hb : d62809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62804 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6108 q ha hb
    | true =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62805 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62806 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62807 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62808 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62809 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6110 (p : Pattern) (ha : d62374 p = 1) (hb : d62815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62810 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6109 q ha hb
    | true =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62811 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62812 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62813 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62814 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62815 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6111 (p : Pattern) (ha : d62374 p = 1) (hb : d62821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62374 q = 1) (hb : d62816 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6110 q ha hb
    | true =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62374 q = 1) (hb : d62817 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62374 q = 1) (hb : d62818 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62374 q = 1) (hb : d62819 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62374 q = 1) (hb : d62820 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62374 q = 1) (hb : d62821 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6112 (p : Pattern) (ha : d0 p = 1) (hb : d61538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61538 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6113 (p : Pattern) (ha : d0 p = 1) (hb : d61679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61679 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6114 (p : Pattern) (ha : d62560 p = 1) (hb : d72603 p = 1) : d72925 p = 1 := by
  have h0 (q : Pattern) (ha : d3508 q = 1) (hb : d72603 q = 1) : d3508 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62555 q = 1) (hb : d72602 q = 1) : d62555 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62556 q = 1) (hb : d72603 q = 1) : d72921 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62556, d72603, d72921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62556, d72603, d72921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62557 q = 1) (hb : d72603 q = 1) : d72922 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62557, d72922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62557, d72922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62558 q = 1) (hb : d72603 q = 1) : d72923 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62558, d72923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62558, d72923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62559 q = 1) (hb : d72603 q = 1) : d72924 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62559, d72924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62559, d72924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d62560 q = 1) (hb : d72603 q = 1) : d72925 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62560, d72925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62560, d72925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro6115 (p : Pattern) (ha : d62572 p = 1) (hb : d72603 p = 1) : d72935 p = 1 := by
  have h0 (q : Pattern) (ha : d3521 q = 1) (hb : d72603 q = 1) : d3521 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62567 q = 1) (hb : d72602 q = 1) : d62567 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3524 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62568 q = 1) (hb : d72603 q = 1) : d72931 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62568, d72603, d72931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62568, d72603, d72931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62569 q = 1) (hb : d72603 q = 1) : d72932 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62569, d72932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62569, d72932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62570 q = 1) (hb : d72603 q = 1) : d72933 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62570, d72933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62570, d72933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62571 q = 1) (hb : d72603 q = 1) : d72934 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62571, d72934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62571, d72934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d62572 q = 1) (hb : d72603 q = 1) : d72935 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62572, d72935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62572, d72935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro6116 (p : Pattern) (ha : d62578 p = 1) (hb : d72603 p = 1) : d72941 p = 1 := by
  have h0 (q : Pattern) (ha : d3507 q = 1) (hb : d72603 q = 1) : d3507 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62561 q = 1) (hb : d72603 q = 1) : d72926 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62561, d72926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62561, d72926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6114 q ha hb
  have h3 (q : Pattern) (ha : d62562 q = 1) (hb : d72603 q = 1) : d72927 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62562, d72927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62562, d72927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62563 q = 1) (hb : d72603 q = 1) : d72928 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62563, d72928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62563, d72928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62564 q = 1) (hb : d72603 q = 1) : d72929 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62564, d72929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62564, d72929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62565 q = 1) (hb : d72603 q = 1) : d72930 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62565, d72930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62565, d72930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62573 q = 1) (hb : d72603 q = 1) : d72936 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62573, d72936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62573, d72936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6115 q ha hb
  have h8 (q : Pattern) (ha : d62574 q = 1) (hb : d72603 q = 1) : d72937 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62574, d72937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62574, d72937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62575 q = 1) (hb : d72603 q = 1) : d72938 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62575, d72938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62575, d72938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62576 q = 1) (hb : d72603 q = 1) : d72939 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62576, d72939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62576, d72939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62577 q = 1) (hb : d72603 q = 1) : d72940 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62577, d72940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62577, d72940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62578 q = 1) (hb : d72603 q = 1) : d72941 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62578, d72941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62578, d72941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro6117 (p : Pattern) (ha : d62585 p = 1) (hb : d72603 p = 1) : d72946 p = 1 := by
  have h0 (q : Pattern) (ha : d3536 q = 1) (hb : d72603 q = 1) : d3536 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62580 q = 1) (hb : d72602 q = 1) : d62580 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3540 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62581 q = 1) (hb : d72603 q = 1) : d72942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62581, d72603, d72942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62581, d72603, d72942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62582 q = 1) (hb : d72603 q = 1) : d72943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62582, d72943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62582, d72943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62583 q = 1) (hb : d72603 q = 1) : d72944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62583, d72944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62583, d72944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62584 q = 1) (hb : d72603 q = 1) : d72945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62584, d72945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62584, d72945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d62585 q = 1) (hb : d72603 q = 1) : d72946 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62585, d72946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62585, d72946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro6118 (p : Pattern) (ha : d62591 p = 1) (hb : d72603 p = 1) : d72952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62586 q = 1) (hb : d72603 q = 1) : d72947 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62586, d72947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62586, d72947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6117 q ha hb
  have h2 (q : Pattern) (ha : d62587 q = 1) (hb : d72603 q = 1) : d72948 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62587, d72948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62587, d72948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62588 q = 1) (hb : d72603 q = 1) : d72949 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62588, d72949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62588, d72949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62589 q = 1) (hb : d72603 q = 1) : d72950 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62589, d72950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62589, d72950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62590 q = 1) (hb : d72603 q = 1) : d72951 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62590, d72951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62590, d72951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62591 q = 1) (hb : d72603 q = 1) : d72952 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62591, d72952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62591, d72952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6119 (p : Pattern) (ha : d62599 p = 1) (hb : d72603 p = 1) : d72958 p = 1 := by
  have h0 (q : Pattern) (ha : d3553 q = 1) (hb : d72603 q = 1) : d3553 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62594 q = 1) (hb : d72602 q = 1) : d62594 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3557 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62595 q = 1) (hb : d72603 q = 1) : d72954 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62595, d72603, d72954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62595, d72603, d72954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62596 q = 1) (hb : d72603 q = 1) : d72955 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62596, d72955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62596, d72955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62597 q = 1) (hb : d72603 q = 1) : d72956 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62597, d72956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62597, d72956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62598 q = 1) (hb : d72603 q = 1) : d72957 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62598, d72957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62598, d72957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d62599 q = 1) (hb : d72603 q = 1) : d72958 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62599, d72958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62599, d72958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro6120 (p : Pattern) (ha : d62605 p = 1) (hb : d72603 p = 1) : d72964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62600 q = 1) (hb : d72603 q = 1) : d72959 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62600, d72959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62600, d72959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6119 q ha hb
  have h2 (q : Pattern) (ha : d62601 q = 1) (hb : d72603 q = 1) : d72960 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62601, d72960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62601, d72960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62602 q = 1) (hb : d72603 q = 1) : d72961 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62602, d72961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62602, d72961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62603 q = 1) (hb : d72603 q = 1) : d72962 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62603, d72962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62603, d72962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62604 q = 1) (hb : d72603 q = 1) : d72963 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62604, d72963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62604, d72963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62605 q = 1) (hb : d72603 q = 1) : d72964 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62605, d72964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62605, d72964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6121 (p : Pattern) (ha : d62614 p = 1) (hb : d72603 p = 1) : d72971 p = 1 := by
  have h0 (q : Pattern) (ha : d3571 q = 1) (hb : d72603 q = 1) : d3571 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62609 q = 1) (hb : d72602 q = 1) : d62609 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62610 q = 1) (hb : d72603 q = 1) : d72967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62610, d72603, d72967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62610, d72603, d72967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62611 q = 1) (hb : d72603 q = 1) : d72968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62611, d72968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62611, d72968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62612 q = 1) (hb : d72603 q = 1) : d72969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62612, d72969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62612, d72969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62613 q = 1) (hb : d72603 q = 1) : d72970 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62613, d72970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62613, d72970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d62614 q = 1) (hb : d72603 q = 1) : d72971 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62614, d72971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62614, d72971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro6122 (p : Pattern) (ha : d62620 p = 1) (hb : d72603 p = 1) : d72977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62615 q = 1) (hb : d72603 q = 1) : d72972 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62615, d72972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62615, d72972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6121 q ha hb
  have h2 (q : Pattern) (ha : d62616 q = 1) (hb : d72603 q = 1) : d72973 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62616, d72973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62616, d72973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62617 q = 1) (hb : d72603 q = 1) : d72974 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62617, d72974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62617, d72974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62618 q = 1) (hb : d72603 q = 1) : d72975 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62618, d72975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62618, d72975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62619 q = 1) (hb : d72603 q = 1) : d72976 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62619, d72976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62619, d72976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62620 q = 1) (hb : d72603 q = 1) : d72977 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62620, d72977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62620, d72977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6123 (p : Pattern) (ha : d62630 p = 1) (hb : d72603 p = 1) : d72985 p = 1 := by
  have h0 (q : Pattern) (ha : d3590 q = 1) (hb : d72603 q = 1) : d3590 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62625 q = 1) (hb : d72602 q = 1) : d62625 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62626 q = 1) (hb : d72603 q = 1) : d72981 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62626, d72603, d72981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62626, d72603, d72981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62627 q = 1) (hb : d72603 q = 1) : d72982 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62627, d72982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62627, d72982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62628 q = 1) (hb : d72603 q = 1) : d72983 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62628, d72983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62628, d72983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62629 q = 1) (hb : d72603 q = 1) : d72984 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62629, d72984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62629, d72984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d62630 q = 1) (hb : d72603 q = 1) : d72985 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62630, d72985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62630, d72985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro6124 (p : Pattern) (ha : d62636 p = 1) (hb : d72603 p = 1) : d72991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62631 q = 1) (hb : d72603 q = 1) : d72986 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62631, d72986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62631, d72986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6123 q ha hb
  have h2 (q : Pattern) (ha : d62632 q = 1) (hb : d72603 q = 1) : d72987 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62632, d72987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62632, d72987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62633 q = 1) (hb : d72603 q = 1) : d72988 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62633, d72988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62633, d72988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62634 q = 1) (hb : d72603 q = 1) : d72989 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62634, d72989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62634, d72989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62635 q = 1) (hb : d72603 q = 1) : d72990 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62635, d72990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62635, d72990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62636 q = 1) (hb : d72603 q = 1) : d72991 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62636, d72991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62636, d72991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6125 (p : Pattern) (ha : d62647 p = 1) (hb : d72603 p = 1) : d73000 p = 1 := by
  have h0 (q : Pattern) (ha : d3610 q = 1) (hb : d72603 q = 1) : d3610 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62642 q = 1) (hb : d72602 q = 1) : d62642 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d62643 q = 1) (hb : d72603 q = 1) : d72996 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62643, d72603, d72996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62643, d72603, d72996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62644 q = 1) (hb : d72603 q = 1) : d72997 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62644, d72997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62644, d72997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62645 q = 1) (hb : d72603 q = 1) : d72998 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62645, d72998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62645, d72998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62646 q = 1) (hb : d72603 q = 1) : d72999 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62646, d72999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62646, d72999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d62647 q = 1) (hb : d72603 q = 1) : d73000 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62647, d73000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d62647, d73000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro6126 (p : Pattern) (ha : d62653 p = 1) (hb : d72603 p = 1) : d73006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62648 q = 1) (hb : d72603 q = 1) : d73001 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62648, d73001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62648, d73001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6125 q ha hb
  have h2 (q : Pattern) (ha : d62649 q = 1) (hb : d72603 q = 1) : d73002 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62649, d73002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62649, d73002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62650 q = 1) (hb : d72603 q = 1) : d73003 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62650, d73003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62650, d73003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62651 q = 1) (hb : d72603 q = 1) : d73004 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62651, d73004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62651, d73004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62652 q = 1) (hb : d72603 q = 1) : d73005 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62652, d73005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62652, d73005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62653 q = 1) (hb : d72603 q = 1) : d73006 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62653, d73006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62653, d73006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6127 (p : Pattern) (ha : d62659 p = 1) (hb : d72603 p = 1) : d73012 p = 1 := by
  have h0 (q : Pattern) (ha : d62592 q = 1) (hb : d72603 q = 1) : d72953 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62592, d72953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6116 q ha hb
    | true =>
      simp only [d62592, d72953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6118 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62606 q = 1) (hb : d72603 q = 1) : d72965 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62606, d72965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62606, d72965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6120 q ha hb
  have h3 (q : Pattern) (ha : d62607 q = 1) (hb : d72603 q = 1) : d72966 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62607, d72966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62607, d72966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62621 q = 1) (hb : d72603 q = 1) : d72978 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62621, d72978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62621, d72978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6122 q ha hb
  have h5 (q : Pattern) (ha : d62622 q = 1) (hb : d72603 q = 1) : d72979 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62622, d72979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62622, d72979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62623 q = 1) (hb : d72603 q = 1) : d72980 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62623, d72980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62623, d72980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62637 q = 1) (hb : d72603 q = 1) : d72992 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62637, d72992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62637, d72992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6124 q ha hb
  have h8 (q : Pattern) (ha : d62638 q = 1) (hb : d72603 q = 1) : d72993 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62638, d72993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62638, d72993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62639 q = 1) (hb : d72603 q = 1) : d72994 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62639, d72994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62639, d72994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62640 q = 1) (hb : d72603 q = 1) : d72995 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62640, d72995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62640, d72995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62654 q = 1) (hb : d72603 q = 1) : d73007 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62654, d73007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62654, d73007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6126 q ha hb
  have h12 (q : Pattern) (ha : d62655 q = 1) (hb : d72603 q = 1) : d73008 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62655, d73008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62655, d73008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62656 q = 1) (hb : d72603 q = 1) : d73009 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62656, d73009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62656, d73009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62657 q = 1) (hb : d72603 q = 1) : d73010 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62657, d73010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62657, d73010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62658 q = 1) (hb : d72603 q = 1) : d73011 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62658, d73011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62658, d73011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62659 q = 1) (hb : d72603 q = 1) : d73012 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62659, d73012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62659, d73012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6128 (p : Pattern) (ha : d62665 p = 1) (hb : d72603 p = 1) : d73018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62660 q = 1) (hb : d72603 q = 1) : d73013 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62660, d73013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6127 q ha hb
    | true =>
      simp only [d62660, d73013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62661 q = 1) (hb : d72603 q = 1) : d73014 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62661, d73014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62661, d73014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62662 q = 1) (hb : d72603 q = 1) : d73015 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62662, d73015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62662, d73015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62663 q = 1) (hb : d72603 q = 1) : d73016 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62663, d73016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62663, d73016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62664 q = 1) (hb : d72603 q = 1) : d73017 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62664, d73017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62664, d73017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62665 q = 1) (hb : d72603 q = 1) : d73018 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62665, d73018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62665, d73018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6129 (p : Pattern) (ha : d62671 p = 1) (hb : d72603 p = 1) : d73024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62666 q = 1) (hb : d72603 q = 1) : d73019 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62666, d73019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6128 q ha hb
    | true =>
      simp only [d62666, d73019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62667 q = 1) (hb : d72603 q = 1) : d73020 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62667, d73020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62667, d73020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62668 q = 1) (hb : d72603 q = 1) : d73021 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62668, d73021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62668, d73021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62669 q = 1) (hb : d72603 q = 1) : d73022 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62669, d73022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62669, d73022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62670 q = 1) (hb : d72603 q = 1) : d73023 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62670, d73023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62670, d73023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62671 q = 1) (hb : d72603 q = 1) : d73024 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62671, d73024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62671, d73024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6130 (p : Pattern) (ha : d62677 p = 1) (hb : d72603 p = 1) : d73030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62672 q = 1) (hb : d72603 q = 1) : d73025 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62672, d73025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6129 q ha hb
    | true =>
      simp only [d62672, d73025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62673 q = 1) (hb : d72603 q = 1) : d73026 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62673, d73026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62673, d73026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62674 q = 1) (hb : d72603 q = 1) : d73027 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62674, d73027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62674, d73027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62675 q = 1) (hb : d72603 q = 1) : d73028 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62675, d73028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62675, d73028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62676 q = 1) (hb : d72603 q = 1) : d73029 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62676, d73029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62676, d73029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62677 q = 1) (hb : d72603 q = 1) : d73030 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62677, d73030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62677, d73030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6131 (p : Pattern) (ha : d62683 p = 1) (hb : d72603 p = 1) : d73036 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62678 q = 1) (hb : d72603 q = 1) : d73031 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62678, d73031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6130 q ha hb
    | true =>
      simp only [d62678, d73031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62679 q = 1) (hb : d72603 q = 1) : d73032 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62679, d73032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62679, d73032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62680 q = 1) (hb : d72603 q = 1) : d73033 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62680, d73033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62680, d73033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62681 q = 1) (hb : d72603 q = 1) : d73034 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62681, d73034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62681, d73034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62682 q = 1) (hb : d72603 q = 1) : d73035 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62682, d73035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62682, d73035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62683 q = 1) (hb : d72603 q = 1) : d73036 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62683, d73036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62683, d73036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6132 (p : Pattern) (ha : d62689 p = 1) (hb : d72603 p = 1) : d73042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62684 q = 1) (hb : d72603 q = 1) : d73037 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62684, d73037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6131 q ha hb
    | true =>
      simp only [d62684, d73037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62685 q = 1) (hb : d72603 q = 1) : d73038 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62685, d73038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62685, d73038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62686 q = 1) (hb : d72603 q = 1) : d73039 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62686, d73039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62686, d73039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62687 q = 1) (hb : d72603 q = 1) : d73040 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62687, d73040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62687, d73040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62688 q = 1) (hb : d72603 q = 1) : d73041 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62688, d73041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62688, d73041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62689 q = 1) (hb : d72603 q = 1) : d73042 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62689, d73042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62689, d73042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6133 (p : Pattern) (ha : d62695 p = 1) (hb : d72603 p = 1) : d73048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62690 q = 1) (hb : d72603 q = 1) : d73043 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62690, d73043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6132 q ha hb
    | true =>
      simp only [d62690, d73043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62691 q = 1) (hb : d72603 q = 1) : d73044 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62691, d73044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62691, d73044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62692 q = 1) (hb : d72603 q = 1) : d73045 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62692, d73045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62692, d73045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62693 q = 1) (hb : d72603 q = 1) : d73046 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62693, d73046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62693, d73046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62694 q = 1) (hb : d72603 q = 1) : d73047 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62694, d73047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62694, d73047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62695 q = 1) (hb : d72603 q = 1) : d73048 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62695, d73048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62695, d73048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6134 (p : Pattern) (ha : d62701 p = 1) (hb : d72603 p = 1) : d73054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d72603 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62696 q = 1) (hb : d72603 q = 1) : d73049 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62696, d73049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6133 q ha hb
    | true =>
      simp only [d62696, d73049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62697 q = 1) (hb : d72603 q = 1) : d73050 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62697, d73050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62697, d73050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62698 q = 1) (hb : d72603 q = 1) : d73051 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62698, d73051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62698, d73051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62699 q = 1) (hb : d72603 q = 1) : d73052 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62699, d73052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62699, d73052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62700 q = 1) (hb : d72603 q = 1) : d73053 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62700, d73053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62700, d73053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62701 q = 1) (hb : d72603 q = 1) : d73054 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62701, d73054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62701, d73054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6135 (p : Pattern) (ha : d73054 p = 1) (hb : d74036 p = 1) : d73054 p = 1 := by
  have h0 (q : Pattern) (ha : d73054 q = 1) (hb : d74036 q = 1) : d73054 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6136 (p : Pattern) (ha : d62821 p = 1) (hb : d72603 p = 1) : d62821 p = 1 := by
  have h0 (q : Pattern) (ha : d62821 q = 1) (hb : d72603 q = 1) : d62821 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6137 (p : Pattern) (ha : d62704 p = 1) (hb : d73913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52031 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d52031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
  have h3 (q : Pattern) (ha : d2526 q = 1) (hb : d52031 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2527 q = 1) (hb : d73910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d73910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2527, d73910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62702 q = 1) (hb : d73911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62702, d73911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62702, d73911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62703 q = 1) (hb : d73912 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62703, d73912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62703, d73912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d62704 q = 1) (hb : d73913 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62704, d73913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62704, d73913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro6138 (p : Pattern) (ha : d62712 p = 1) (hb : d73922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5739 q ha hb
  have h3 (q : Pattern) (ha : d2538 q = 1) (hb : d52163 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2539 q = 1) (hb : d73919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d73919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2539, d73919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62710 q = 1) (hb : d73920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62710, d73920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62710, d73920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62711 q = 1) (hb : d73921 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62711, d73921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62711, d73921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d62712 q = 1) (hb : d73922 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62712, d73922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62712, d73922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro6139 (p : Pattern) (ha : d62718 p = 1) (hb : d73928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62705 q = 1) (hb : d73914 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62705, d73914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62705, d73914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6137 q ha hb
  have h2 (q : Pattern) (ha : d62706 q = 1) (hb : d73915 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62706, d73915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62706, d73915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62707 q = 1) (hb : d73916 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62707, d73916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62707, d73916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62708 q = 1) (hb : d73917 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62708, d73917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62708, d73917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62709 q = 1) (hb : d73918 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62709, d73918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62709, d73918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62713 q = 1) (hb : d73923 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62713, d73923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62713, d73923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6138 q ha hb
  have h7 (q : Pattern) (ha : d62714 q = 1) (hb : d73924 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62714, d73924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62714, d73924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62715 q = 1) (hb : d73925 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62715, d73925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62715, d73925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62716 q = 1) (hb : d73926 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62716, d73926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62716, d73926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62717 q = 1) (hb : d73927 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62717, d73927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62717, d73927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62718 q = 1) (hb : d73928 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62718, d73928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62718, d73928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6140 (p : Pattern) (ha : d62721 p = 1) (hb : d73932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d52342 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5744 q ha hb
  have h3 (q : Pattern) (ha : d2551 q = 1) (hb : d52342 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2552 q = 1) (hb : d73929 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d73929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2552, d73929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62719 q = 1) (hb : d73930 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62719, d73930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62719, d73930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62720 q = 1) (hb : d73931 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62720, d73931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62720, d73931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d62721 q = 1) (hb : d73932 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62721, d73932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62721, d73932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro6141 (p : Pattern) (ha : d62727 p = 1) (hb : d73938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62722 q = 1) (hb : d73933 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62722, d73933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62722, d73933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6140 q ha hb
  have h2 (q : Pattern) (ha : d62723 q = 1) (hb : d73934 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62723, d73934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62723, d73934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62724 q = 1) (hb : d73935 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62724, d73935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62724, d73935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62725 q = 1) (hb : d73936 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62725, d73936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62725, d73936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62726 q = 1) (hb : d73937 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62726, d73937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62726, d73937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62727 q = 1) (hb : d73938 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62727, d73938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62727, d73938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6142 (p : Pattern) (ha : d62731 p = 1) (hb : d73943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52563 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d52563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5750 q ha hb
  have h3 (q : Pattern) (ha : d2565 q = 1) (hb : d52563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2566 q = 1) (hb : d73940 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d73940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2566, d73940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62729 q = 1) (hb : d73941 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62729, d73941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62729, d73941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62730 q = 1) (hb : d73942 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62730, d73942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62730, d73942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d62731 q = 1) (hb : d73943 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62731, d73943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62731, d73943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro6143 (p : Pattern) (ha : d62737 p = 1) (hb : d73949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62732 q = 1) (hb : d73944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62732, d73944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62732, d73944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6142 q ha hb
  have h2 (q : Pattern) (ha : d62733 q = 1) (hb : d73945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62733, d73945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62733, d73945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62734 q = 1) (hb : d73946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62734, d73946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62734, d73946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62735 q = 1) (hb : d73947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62735, d73947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62735, d73947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62736 q = 1) (hb : d73948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62736, d73948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62736, d73948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62737 q = 1) (hb : d73949 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62737, d73949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62737, d73949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6144 (p : Pattern) (ha : d62742 p = 1) (hb : d73955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d52843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5756 q ha hb
  have h3 (q : Pattern) (ha : d2580 q = 1) (hb : d52843 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2581 q = 1) (hb : d73952 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d73952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2581, d73952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62740 q = 1) (hb : d73953 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62740, d73953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62740, d73953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62741 q = 1) (hb : d73954 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62741, d73954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62741, d73954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d62742 q = 1) (hb : d73955 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62742, d73955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62742, d73955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro6145 (p : Pattern) (ha : d62748 p = 1) (hb : d73961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62743 q = 1) (hb : d73956 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62743, d73956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62743, d73956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6144 q ha hb
  have h2 (q : Pattern) (ha : d62744 q = 1) (hb : d73957 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62744, d73957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62744, d73957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62745 q = 1) (hb : d73958 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62745, d73958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62745, d73958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62746 q = 1) (hb : d73959 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62746, d73959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62746, d73959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62747 q = 1) (hb : d73960 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62747, d73960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62747, d73960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62748 q = 1) (hb : d73961 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62748, d73961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62748, d73961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6146 (p : Pattern) (ha : d62754 p = 1) (hb : d73968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d53158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5762 q ha hb
  have h3 (q : Pattern) (ha : d2596 q = 1) (hb : d53158 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2597 q = 1) (hb : d73965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d73965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2597, d73965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62752 q = 1) (hb : d73966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62752, d73966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62752, d73966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62753 q = 1) (hb : d73967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62753, d73967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62753, d73967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d62754 q = 1) (hb : d73968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62754, d73968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62754, d73968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro6147 (p : Pattern) (ha : d62760 p = 1) (hb : d73974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62755 q = 1) (hb : d73969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62755, d73969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62755, d73969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6146 q ha hb
  have h2 (q : Pattern) (ha : d62756 q = 1) (hb : d73970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62756, d73970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62756, d73970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62757 q = 1) (hb : d73971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62757, d73971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62757, d73971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62758 q = 1) (hb : d73972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62758, d73972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62758, d73972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62759 q = 1) (hb : d73973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62759, d73973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62759, d73973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62760 q = 1) (hb : d73974 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62760, d73974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62760, d73974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6148 (p : Pattern) (ha : d62767 p = 1) (hb : d73982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53475 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d53475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5768 q ha hb
  have h3 (q : Pattern) (ha : d2613 q = 1) (hb : d53475 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d2614 q = 1) (hb : d73979 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d73979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2614, d73979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62765 q = 1) (hb : d73980 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62765, d73980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62765, d73980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62766 q = 1) (hb : d73981 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62766, d73981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62766, d73981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d62767 q = 1) (hb : d73982 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62767, d73982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62767, d73982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro6149 (p : Pattern) (ha : d62773 p = 1) (hb : d73988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62768 q = 1) (hb : d73983 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62768, d73983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62768, d73983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6148 q ha hb
  have h2 (q : Pattern) (ha : d62769 q = 1) (hb : d73984 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62769, d73984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62769, d73984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62770 q = 1) (hb : d73985 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62770, d73985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62770, d73985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62771 q = 1) (hb : d73986 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62771, d73986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62771, d73986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62772 q = 1) (hb : d73987 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62772, d73987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62772, d73987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62773 q = 1) (hb : d73988 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62773, d73988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62773, d73988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6150 (p : Pattern) (ha : d62779 p = 1) (hb : d73994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62728 q = 1) (hb : d73939 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62728, d73939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6139 q ha hb
    | true =>
      simp only [d62728, d73939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6141 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62738 q = 1) (hb : d73950 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62738, d73950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62738, d73950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6143 q ha hb
  have h3 (q : Pattern) (ha : d62739 q = 1) (hb : d73951 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62739, d73951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62739, d73951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62749 q = 1) (hb : d73962 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62749, d73962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62749, d73962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6145 q ha hb
  have h5 (q : Pattern) (ha : d62750 q = 1) (hb : d73963 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62750, d73963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62750, d73963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62751 q = 1) (hb : d73964 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62751, d73964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62751, d73964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62761 q = 1) (hb : d73975 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62761, d73975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62761, d73975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6147 q ha hb
  have h8 (q : Pattern) (ha : d62762 q = 1) (hb : d73976 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62762, d73976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62762, d73976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62763 q = 1) (hb : d73977 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62763, d73977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62763, d73977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62764 q = 1) (hb : d73978 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62764, d73978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62764, d73978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62774 q = 1) (hb : d73989 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62774, d73989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62774, d73989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6149 q ha hb
  have h12 (q : Pattern) (ha : d62775 q = 1) (hb : d73990 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62775, d73990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62775, d73990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62776 q = 1) (hb : d73991 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62776, d73991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62776, d73991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62777 q = 1) (hb : d73992 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62777, d73992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62777, d73992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62778 q = 1) (hb : d73993 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62778, d73993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62778, d73993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62779 q = 1) (hb : d73994 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62779, d73994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62779, d73994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6151 (p : Pattern) (ha : d62785 p = 1) (hb : d74000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62780 q = 1) (hb : d73995 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62780, d73995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6150 q ha hb
    | true =>
      simp only [d62780, d73995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62781 q = 1) (hb : d73996 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62781, d73996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62781, d73996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62782 q = 1) (hb : d73997 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62782, d73997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62782, d73997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62783 q = 1) (hb : d73998 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62783, d73998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62783, d73998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62784 q = 1) (hb : d73999 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62784, d73999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62784, d73999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62785 q = 1) (hb : d74000 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62785, d74000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62785, d74000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6152 (p : Pattern) (ha : d62791 p = 1) (hb : d74006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62786 q = 1) (hb : d74001 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62786, d74001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6151 q ha hb
    | true =>
      simp only [d62786, d74001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62787 q = 1) (hb : d74002 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62787, d74002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62787, d74002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62788 q = 1) (hb : d74003 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62788, d74003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62788, d74003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62789 q = 1) (hb : d74004 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62789, d74004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62789, d74004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62790 q = 1) (hb : d74005 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62790, d74005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62790, d74005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62791 q = 1) (hb : d74006 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62791, d74006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62791, d74006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6153 (p : Pattern) (ha : d62797 p = 1) (hb : d74012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62792 q = 1) (hb : d74007 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62792, d74007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6152 q ha hb
    | true =>
      simp only [d62792, d74007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62793 q = 1) (hb : d74008 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62793, d74008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62793, d74008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62794 q = 1) (hb : d74009 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62794, d74009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62794, d74009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62795 q = 1) (hb : d74010 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62795, d74010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62795, d74010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62796 q = 1) (hb : d74011 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62796, d74011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62796, d74011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62797 q = 1) (hb : d74012 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62797, d74012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62797, d74012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6154 (p : Pattern) (ha : d62803 p = 1) (hb : d74018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62798 q = 1) (hb : d74013 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62798, d74013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6153 q ha hb
    | true =>
      simp only [d62798, d74013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62799 q = 1) (hb : d74014 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62799, d74014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62799, d74014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62800 q = 1) (hb : d74015 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62800, d74015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62800, d74015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62801 q = 1) (hb : d74016 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62801, d74016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62801, d74016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62802 q = 1) (hb : d74017 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62802, d74017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62802, d74017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62803 q = 1) (hb : d74018 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62803, d74018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62803, d74018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6155 (p : Pattern) (ha : d62809 p = 1) (hb : d74024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62804 q = 1) (hb : d74019 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62804, d74019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6154 q ha hb
    | true =>
      simp only [d62804, d74019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62805 q = 1) (hb : d74020 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62805, d74020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62805, d74020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62806 q = 1) (hb : d74021 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62806, d74021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62806, d74021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62807 q = 1) (hb : d74022 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62807, d74022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62807, d74022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62808 q = 1) (hb : d74023 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62808, d74023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62808, d74023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62809 q = 1) (hb : d74024 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62809, d74024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62809, d74024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6156 (p : Pattern) (ha : d62815 p = 1) (hb : d74030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62810 q = 1) (hb : d74025 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62810, d74025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6155 q ha hb
    | true =>
      simp only [d62810, d74025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62811 q = 1) (hb : d74026 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62811, d74026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62811, d74026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62812 q = 1) (hb : d74027 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62812, d74027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62812, d74027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62813 q = 1) (hb : d74028 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62813, d74028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62813, d74028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62814 q = 1) (hb : d74029 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62814, d74029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62814, d74029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62815 q = 1) (hb : d74030 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62815, d74030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62815, d74030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6157 (p : Pattern) (ha : d62821 p = 1) (hb : d74036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62816 q = 1) (hb : d74031 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62816, d74031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6156 q ha hb
    | true =>
      simp only [d62816, d74031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62817 q = 1) (hb : d74032 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62817, d74032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62817, d74032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62818 q = 1) (hb : d74033 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62818, d74033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62818, d74033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62819 q = 1) (hb : d74034 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62819, d74034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62819, d74034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62820 q = 1) (hb : d74035 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62820, d74035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62820, d74035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62821 q = 1) (hb : d74036 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62821, d74036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62821, d74036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6158 (p : Pattern) (ha : d62821 p = 1) (hb : d73909 p = 1) : d62821 p = 1 := by
  have h0 (q : Pattern) (ha : d62821 q = 1) (hb : d73909 q = 1) : d62821 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6159 (p : Pattern) (ha : d3503 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d3500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3501 q = 1) (hb : d64964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3501, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3502 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3502, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3503 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6160 (p : Pattern) (ha : d62560 p = 1) (hb : d64965 p = 1) : d64968 p = 1 := by
  have h0 (q : Pattern) (ha : d3508 q = 1) (hb : d54978 q = 1) : d3508 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62558 q = 1) (hb : d64964 q = 1) : d64966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62558, d64964, d64966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62558, d64964, d64966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62559 q = 1) (hb : d64965 q = 1) : d64967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62559, d64965, d64967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62559, d64965, d64967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62560 q = 1) (hb : d64965 q = 1) : d64968 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62560, d64968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62560, d64968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6161 (p : Pattern) (ha : d62572 p = 1) (hb : d64965 p = 1) : d64976 p = 1 := by
  have h0 (q : Pattern) (ha : d3521 q = 1) (hb : d54978 q = 1) : d3521 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62569 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62570 q = 1) (hb : d64964 q = 1) : d64974 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62570, d64964, d64974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62570, d64964, d64974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62571 q = 1) (hb : d64965 q = 1) : d64975 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62571, d64965, d64975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62571, d64965, d64975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62572 q = 1) (hb : d64965 q = 1) : d64976 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62572, d64976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62572, d64976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6162 (p : Pattern) (ha : d62578 p = 1) (hb : d64965 p = 1) : d64982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3504 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6159 q ha hb
  have h2 (q : Pattern) (ha : d3505 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3506 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3507 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62561 q = 1) (hb : d64965 q = 1) : d64969 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62561, d64969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62561, d64969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6160 q ha hb
  have h6 (q : Pattern) (ha : d62562 q = 1) (hb : d64965 q = 1) : d64970 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62562, d64970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62562, d64970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62563 q = 1) (hb : d64965 q = 1) : d64971 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62563, d64971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62563, d64971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62564 q = 1) (hb : d64965 q = 1) : d64972 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62564, d64972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62564, d64972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62565 q = 1) (hb : d64965 q = 1) : d64973 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62565, d64973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62565, d64973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62573 q = 1) (hb : d64965 q = 1) : d64977 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62573, d64977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62573, d64977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6161 q ha hb
  have h11 (q : Pattern) (ha : d62574 q = 1) (hb : d64965 q = 1) : d64978 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62574, d64978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62574, d64978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62575 q = 1) (hb : d64965 q = 1) : d64979 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62575, d64979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62575, d64979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62576 q = 1) (hb : d64965 q = 1) : d64980 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62576, d64980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62576, d64980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62577 q = 1) (hb : d64965 q = 1) : d64981 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62577, d64981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62577, d64981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62578 q = 1) (hb : d64965 q = 1) : d64982 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62578, d64982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62578, d64982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6163 (p : Pattern) (ha : d62585 p = 1) (hb : d64965 p = 1) : d64985 p = 1 := by
  have h0 (q : Pattern) (ha : d3536 q = 1) (hb : d54978 q = 1) : d3536 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62583 q = 1) (hb : d64964 q = 1) : d64983 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62583, d64964, d64983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62583, d64964, d64983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62584 q = 1) (hb : d64965 q = 1) : d64984 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62584, d64965, d64984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62584, d64965, d64984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62585 q = 1) (hb : d64965 q = 1) : d64985 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62585, d64985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62585, d64985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6164 (p : Pattern) (ha : d62591 p = 1) (hb : d64965 p = 1) : d64991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62586 q = 1) (hb : d64965 q = 1) : d64986 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62586, d64986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62586, d64986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6163 q ha hb
  have h2 (q : Pattern) (ha : d62587 q = 1) (hb : d64965 q = 1) : d64987 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62587, d64987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62587, d64987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62588 q = 1) (hb : d64965 q = 1) : d64988 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62588, d64988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62588, d64988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62589 q = 1) (hb : d64965 q = 1) : d64989 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62589, d64989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62589, d64989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62590 q = 1) (hb : d64965 q = 1) : d64990 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62590, d64990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62590, d64990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62591 q = 1) (hb : d64965 q = 1) : d64991 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62591, d64991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62591, d64991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6165 (p : Pattern) (ha : d62599 p = 1) (hb : d64965 p = 1) : d64995 p = 1 := by
  have h0 (q : Pattern) (ha : d3553 q = 1) (hb : d54978 q = 1) : d3553 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62596 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62597 q = 1) (hb : d64964 q = 1) : d64993 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62597, d64964, d64993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62597, d64964, d64993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62598 q = 1) (hb : d64965 q = 1) : d64994 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62598, d64965, d64994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62598, d64965, d64994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62599 q = 1) (hb : d64965 q = 1) : d64995 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62599, d64995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62599, d64995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6166 (p : Pattern) (ha : d62605 p = 1) (hb : d64965 p = 1) : d65001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62600 q = 1) (hb : d64965 q = 1) : d64996 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62600, d64996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62600, d64996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6165 q ha hb
  have h2 (q : Pattern) (ha : d62601 q = 1) (hb : d64965 q = 1) : d64997 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62601, d64997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62601, d64997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62602 q = 1) (hb : d64965 q = 1) : d64998 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62602, d64998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62602, d64998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62603 q = 1) (hb : d64965 q = 1) : d64999 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62603, d64999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62603, d64999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62604 q = 1) (hb : d64965 q = 1) : d65000 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62604, d65000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62604, d65000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62605 q = 1) (hb : d64965 q = 1) : d65001 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62605, d65001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62605, d65001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6167 (p : Pattern) (ha : d62614 p = 1) (hb : d64965 p = 1) : d65006 p = 1 := by
  have h0 (q : Pattern) (ha : d3571 q = 1) (hb : d54978 q = 1) : d3571 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62612 q = 1) (hb : d64964 q = 1) : d65004 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62612, d64964, d65004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62612, d64964, d65004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62613 q = 1) (hb : d64965 q = 1) : d65005 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62613, d64965, d65005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62613, d64965, d65005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62614 q = 1) (hb : d64965 q = 1) : d65006 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62614, d65006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62614, d65006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6168 (p : Pattern) (ha : d62620 p = 1) (hb : d64965 p = 1) : d65012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62615 q = 1) (hb : d64965 q = 1) : d65007 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62615, d65007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62615, d65007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6167 q ha hb
  have h2 (q : Pattern) (ha : d62616 q = 1) (hb : d64965 q = 1) : d65008 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62616, d65008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62616, d65008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62617 q = 1) (hb : d64965 q = 1) : d65009 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62617, d65009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62617, d65009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62618 q = 1) (hb : d64965 q = 1) : d65010 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62618, d65010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62618, d65010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62619 q = 1) (hb : d64965 q = 1) : d65011 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62619, d65011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62619, d65011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62620 q = 1) (hb : d64965 q = 1) : d65012 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62620, d65012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62620, d65012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6169 (p : Pattern) (ha : d62630 p = 1) (hb : d64965 p = 1) : d65018 p = 1 := by
  have h0 (q : Pattern) (ha : d3590 q = 1) (hb : d54978 q = 1) : d3590 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62627 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62628 q = 1) (hb : d64964 q = 1) : d65016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62628, d64964, d65016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62628, d64964, d65016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62629 q = 1) (hb : d64965 q = 1) : d65017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62629, d64965, d65017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62629, d64965, d65017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62630 q = 1) (hb : d64965 q = 1) : d65018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62630, d65018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62630, d65018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6170 (p : Pattern) (ha : d62636 p = 1) (hb : d64965 p = 1) : d65024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62631 q = 1) (hb : d64965 q = 1) : d65019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62631, d65019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62631, d65019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6169 q ha hb
  have h2 (q : Pattern) (ha : d62632 q = 1) (hb : d64965 q = 1) : d65020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62632, d65020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62632, d65020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62633 q = 1) (hb : d64965 q = 1) : d65021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62633, d65021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62633, d65021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62634 q = 1) (hb : d64965 q = 1) : d65022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62634, d65022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62634, d65022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62635 q = 1) (hb : d64965 q = 1) : d65023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62635, d65023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62635, d65023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62636 q = 1) (hb : d64965 q = 1) : d65024 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62636, d65024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62636, d65024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6171 (p : Pattern) (ha : d62647 p = 1) (hb : d64965 p = 1) : d65031 p = 1 := by
  have h0 (q : Pattern) (ha : d3610 q = 1) (hb : d54978 q = 1) : d3610 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d62644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62645 q = 1) (hb : d64964 q = 1) : d65029 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62645, d64964, d65029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62645, d64964, d65029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62646 q = 1) (hb : d64965 q = 1) : d65030 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62646, d64965, d65030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62646, d64965, d65030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62647 q = 1) (hb : d64965 q = 1) : d65031 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62647, d65031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62647, d65031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6172 (p : Pattern) (ha : d62653 p = 1) (hb : d64965 p = 1) : d65037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62648 q = 1) (hb : d64965 q = 1) : d65032 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62648, d65032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62648, d65032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6171 q ha hb
  have h2 (q : Pattern) (ha : d62649 q = 1) (hb : d64965 q = 1) : d65033 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62649, d65033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62649, d65033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62650 q = 1) (hb : d64965 q = 1) : d65034 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62650, d65034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62650, d65034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62651 q = 1) (hb : d64965 q = 1) : d65035 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62651, d65035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62651, d65035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62652 q = 1) (hb : d64965 q = 1) : d65036 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62652, d65036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62652, d65036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62653 q = 1) (hb : d64965 q = 1) : d65037 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62653, d65037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62653, d65037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6173 (p : Pattern) (ha : d62659 p = 1) (hb : d64965 p = 1) : d65043 p = 1 := by
  have h0 (q : Pattern) (ha : d62592 q = 1) (hb : d64965 q = 1) : d64992 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62592, d64992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6162 q ha hb
    | true =>
      simp only [d62592, d64992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6164 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62606 q = 1) (hb : d64965 q = 1) : d65002 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62606, d65002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62606, d65002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6166 q ha hb
  have h3 (q : Pattern) (ha : d62607 q = 1) (hb : d64965 q = 1) : d65003 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62607, d65003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62607, d65003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62621 q = 1) (hb : d64965 q = 1) : d65013 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62621, d65013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62621, d65013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6168 q ha hb
  have h5 (q : Pattern) (ha : d62622 q = 1) (hb : d64965 q = 1) : d65014 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62622, d65014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62622, d65014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62623 q = 1) (hb : d64965 q = 1) : d65015 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62623, d65015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62623, d65015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62637 q = 1) (hb : d64965 q = 1) : d65025 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62637, d65025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62637, d65025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6170 q ha hb
  have h8 (q : Pattern) (ha : d62638 q = 1) (hb : d64965 q = 1) : d65026 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62638, d65026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62638, d65026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62639 q = 1) (hb : d64965 q = 1) : d65027 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62639, d65027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62639, d65027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62640 q = 1) (hb : d64965 q = 1) : d65028 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62640, d65028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62640, d65028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62654 q = 1) (hb : d64965 q = 1) : d65038 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62654, d65038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62654, d65038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6172 q ha hb
  have h12 (q : Pattern) (ha : d62655 q = 1) (hb : d64965 q = 1) : d65039 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62655, d65039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62655, d65039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62656 q = 1) (hb : d64965 q = 1) : d65040 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62656, d65040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62656, d65040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62657 q = 1) (hb : d64965 q = 1) : d65041 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62657, d65041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62657, d65041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62658 q = 1) (hb : d64965 q = 1) : d65042 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62658, d65042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62658, d65042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62659 q = 1) (hb : d64965 q = 1) : d65043 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62659, d65043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62659, d65043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6174 (p : Pattern) (ha : d62665 p = 1) (hb : d64965 p = 1) : d65049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62660 q = 1) (hb : d64965 q = 1) : d65044 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62660, d65044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6173 q ha hb
    | true =>
      simp only [d62660, d65044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62661 q = 1) (hb : d64965 q = 1) : d65045 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62661, d65045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62661, d65045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62662 q = 1) (hb : d64965 q = 1) : d65046 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62662, d65046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62662, d65046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62663 q = 1) (hb : d64965 q = 1) : d65047 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62663, d65047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62663, d65047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62664 q = 1) (hb : d64965 q = 1) : d65048 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62664, d65048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62664, d65048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62665 q = 1) (hb : d64965 q = 1) : d65049 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62665, d65049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62665, d65049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6175 (p : Pattern) (ha : d62671 p = 1) (hb : d64965 p = 1) : d65055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62666 q = 1) (hb : d64965 q = 1) : d65050 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62666, d65050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6174 q ha hb
    | true =>
      simp only [d62666, d65050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62667 q = 1) (hb : d64965 q = 1) : d65051 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62667, d65051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62667, d65051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62668 q = 1) (hb : d64965 q = 1) : d65052 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62668, d65052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62668, d65052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62669 q = 1) (hb : d64965 q = 1) : d65053 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62669, d65053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62669, d65053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62670 q = 1) (hb : d64965 q = 1) : d65054 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62670, d65054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62670, d65054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62671 q = 1) (hb : d64965 q = 1) : d65055 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62671, d65055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62671, d65055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6176 (p : Pattern) (ha : d62677 p = 1) (hb : d64965 p = 1) : d65061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62672 q = 1) (hb : d64965 q = 1) : d65056 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62672, d65056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6175 q ha hb
    | true =>
      simp only [d62672, d65056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62673 q = 1) (hb : d64965 q = 1) : d65057 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62673, d65057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62673, d65057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62674 q = 1) (hb : d64965 q = 1) : d65058 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62674, d65058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62674, d65058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62675 q = 1) (hb : d64965 q = 1) : d65059 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62675, d65059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62675, d65059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62676 q = 1) (hb : d64965 q = 1) : d65060 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62676, d65060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62676, d65060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62677 q = 1) (hb : d64965 q = 1) : d65061 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62677, d65061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62677, d65061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6177 (p : Pattern) (ha : d62683 p = 1) (hb : d64965 p = 1) : d65067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62678 q = 1) (hb : d64965 q = 1) : d65062 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62678, d65062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6176 q ha hb
    | true =>
      simp only [d62678, d65062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62679 q = 1) (hb : d64965 q = 1) : d65063 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62679, d65063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62679, d65063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62680 q = 1) (hb : d64965 q = 1) : d65064 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62680, d65064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62680, d65064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62681 q = 1) (hb : d64965 q = 1) : d65065 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62681, d65065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62681, d65065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62682 q = 1) (hb : d64965 q = 1) : d65066 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62682, d65066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62682, d65066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62683 q = 1) (hb : d64965 q = 1) : d65067 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62683, d65067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62683, d65067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6178 (p : Pattern) (ha : d62689 p = 1) (hb : d64965 p = 1) : d65073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62684 q = 1) (hb : d64965 q = 1) : d65068 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62684, d65068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6177 q ha hb
    | true =>
      simp only [d62684, d65068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62685 q = 1) (hb : d64965 q = 1) : d65069 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62685, d65069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62685, d65069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62686 q = 1) (hb : d64965 q = 1) : d65070 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62686, d65070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62686, d65070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62687 q = 1) (hb : d64965 q = 1) : d65071 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62687, d65071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62687, d65071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62688 q = 1) (hb : d64965 q = 1) : d65072 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62688, d65072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62688, d65072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62689 q = 1) (hb : d64965 q = 1) : d65073 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62689, d65073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62689, d65073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6179 (p : Pattern) (ha : d62695 p = 1) (hb : d64965 p = 1) : d65079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62690 q = 1) (hb : d64965 q = 1) : d65074 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62690, d65074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6178 q ha hb
    | true =>
      simp only [d62690, d65074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62691 q = 1) (hb : d64965 q = 1) : d65075 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62691, d65075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62691, d65075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62692 q = 1) (hb : d64965 q = 1) : d65076 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62692, d65076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62692, d65076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62693 q = 1) (hb : d64965 q = 1) : d65077 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62693, d65077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62693, d65077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62694 q = 1) (hb : d64965 q = 1) : d65078 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62694, d65078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62694, d65078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62695 q = 1) (hb : d64965 q = 1) : d65079 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62695, d65079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62695, d65079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6180 (p : Pattern) (ha : d62701 p = 1) (hb : d64965 p = 1) : d65085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62696 q = 1) (hb : d64965 q = 1) : d65080 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62696, d65080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6179 q ha hb
    | true =>
      simp only [d62696, d65080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62697 q = 1) (hb : d64965 q = 1) : d65081 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62697, d65081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62697, d65081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62698 q = 1) (hb : d64965 q = 1) : d65082 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62698, d65082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62698, d65082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62699 q = 1) (hb : d64965 q = 1) : d65083 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62699, d65083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62699, d65083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62700 q = 1) (hb : d64965 q = 1) : d65084 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62700, d65084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62700, d65084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62701 q = 1) (hb : d64965 q = 1) : d65085 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62701, d65085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62701, d65085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6181 (p : Pattern) (ha : d55760 p = 1) (hb : d64968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5735 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3508 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3508, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55758 q = 1) (hb : d64966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55758, d64966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d55758, d64966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55601 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d55759 q = 1) (hb : d64967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55759, d64967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55759, d64967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d55760 q = 1) (hb : d64968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55760, d64968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55760, d64968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h9 p ha hb
theorem andIntro6182 (p : Pattern) (ha : d55768 p = 1) (hb : d64976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52083 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5738 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3521 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3521, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55766 q = 1) (hb : d64974 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55766, d64974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d55766, d64974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55613 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d55767 q = 1) (hb : d64975 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55767, d64975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55767, d64975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d55768 q = 1) (hb : d64976 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55768, d64976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55768, d64976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h9 p ha hb
theorem andIntro6183 (p : Pattern) (ha : d55774 p = 1) (hb : d64982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55761 q = 1) (hb : d64969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55761, d64969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55761, d64969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6181 q ha hb
  have h2 (q : Pattern) (ha : d55762 q = 1) (hb : d64970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55762, d64970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55762, d64970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55763 q = 1) (hb : d64971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55763, d64971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55763, d64971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55764 q = 1) (hb : d64972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55764, d64972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55764, d64972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55765 q = 1) (hb : d64973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55765, d64973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55765, d64973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55769 q = 1) (hb : d64977 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55769, d64977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55769, d64977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6182 q ha hb
  have h7 (q : Pattern) (ha : d55770 q = 1) (hb : d64978 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55770, d64978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55770, d64978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d55771 q = 1) (hb : d64979 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55771, d64979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55771, d64979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d55772 q = 1) (hb : d64980 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55772, d64980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55772, d64980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d55773 q = 1) (hb : d64981 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55773, d64981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55773, d64981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55774 q = 1) (hb : d64982 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55774, d64982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55774, d64982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6184 (p : Pattern) (ha : d55777 p = 1) (hb : d64985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52244 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5743 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3536 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3536, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55775 q = 1) (hb : d64983 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55775, d64983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d55775, d64983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55626 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d55776 q = 1) (hb : d64984 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55776, d64984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55776, d64984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d55777 q = 1) (hb : d64985 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55777, d64985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55777, d64985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h9 p ha hb
theorem andIntro6185 (p : Pattern) (ha : d55783 p = 1) (hb : d64991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55778 q = 1) (hb : d64986 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55778, d64986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55778, d64986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6184 q ha hb
  have h2 (q : Pattern) (ha : d55779 q = 1) (hb : d64987 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55779, d64987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55779, d64987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55780 q = 1) (hb : d64988 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55780, d64988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55780, d64988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55781 q = 1) (hb : d64989 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55781, d64989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55781, d64989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55782 q = 1) (hb : d64990 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55782, d64990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55782, d64990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55783 q = 1) (hb : d64991 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55783, d64991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55783, d64991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6186 (p : Pattern) (ha : d55787 p = 1) (hb : d64995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52466 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5749 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3553 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3553, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55785 q = 1) (hb : d64993 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55785, d64993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d55785, d64993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55640 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d55786 q = 1) (hb : d64994 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55786, d64994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55786, d64994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d55787 q = 1) (hb : d64995 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55787, d64995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55787, d64995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h9 p ha hb
theorem andIntro6187 (p : Pattern) (ha : d55793 p = 1) (hb : d65001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55788 q = 1) (hb : d64996 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55788, d64996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55788, d64996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6186 q ha hb
  have h2 (q : Pattern) (ha : d55789 q = 1) (hb : d64997 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55789, d64997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55789, d64997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55790 q = 1) (hb : d64998 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55790, d64998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55790, d64998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55791 q = 1) (hb : d64999 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55791, d64999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55791, d64999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55792 q = 1) (hb : d65000 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55792, d65000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55792, d65000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55793 q = 1) (hb : d65001 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55793, d65001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55793, d65001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6188 (p : Pattern) (ha : d55798 p = 1) (hb : d65006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52749 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5755 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3571 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3571, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55796 q = 1) (hb : d65004 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55796, d65004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d55796, d65004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55655 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d55797 q = 1) (hb : d65005 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55797, d65005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55797, d65005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d55798 q = 1) (hb : d65006 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55798, d65006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55798, d65006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h9 p ha hb
theorem andIntro6189 (p : Pattern) (ha : d55804 p = 1) (hb : d65012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55799 q = 1) (hb : d65007 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55799, d65007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55799, d65007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6188 q ha hb
  have h2 (q : Pattern) (ha : d55800 q = 1) (hb : d65008 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55800, d65008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55800, d65008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55801 q = 1) (hb : d65009 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55801, d65009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55801, d65009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55802 q = 1) (hb : d65010 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55802, d65010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55802, d65010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55803 q = 1) (hb : d65011 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55803, d65011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55803, d65011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55804 q = 1) (hb : d65012 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55804, d65012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55804, d65012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6190 (p : Pattern) (ha : d55810 p = 1) (hb : d65018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5761 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3590 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3590, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55808 q = 1) (hb : d65016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55808, d65016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d55808, d65016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55671 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d55809 q = 1) (hb : d65017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55809, d65017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55809, d65017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d55810 q = 1) (hb : d65018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55810, d65018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55810, d65018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h9 p ha hb
theorem andIntro6191 (p : Pattern) (ha : d55816 p = 1) (hb : d65024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55811 q = 1) (hb : d65019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55811, d65019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55811, d65019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6190 q ha hb
  have h2 (q : Pattern) (ha : d55812 q = 1) (hb : d65020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55812, d65020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55812, d65020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55813 q = 1) (hb : d65021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55813, d65021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55813, d65021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55814 q = 1) (hb : d65022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55814, d65022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55814, d65022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55815 q = 1) (hb : d65023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55815, d65023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55815, d65023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55816 q = 1) (hb : d65024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55816, d65024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55816, d65024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6192 (p : Pattern) (ha : d55823 p = 1) (hb : d65031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5767 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3610 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55821 q = 1) (hb : d65029 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d55821, d65029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d55821, d65029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55688 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d55822 q = 1) (hb : d65030 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55822, d65030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55822, d65030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d55823 q = 1) (hb : d65031 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55823, d65031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d55823, d65031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h9 p ha hb
theorem andIntro6193 (p : Pattern) (ha : d55829 p = 1) (hb : d65037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55824 q = 1) (hb : d65032 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55824, d65032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55824, d65032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6192 q ha hb
  have h2 (q : Pattern) (ha : d55825 q = 1) (hb : d65033 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55825, d65033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55825, d65033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55826 q = 1) (hb : d65034 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55826, d65034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55826, d65034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55827 q = 1) (hb : d65035 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55827, d65035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55827, d65035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55828 q = 1) (hb : d65036 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55828, d65036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55828, d65036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55829 q = 1) (hb : d65037 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55829, d65037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55829, d65037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6194 (p : Pattern) (ha : d55835 p = 1) (hb : d65043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d55784 q = 1) (hb : d64992 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55784, d64992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6183 q ha hb
    | true =>
      simp only [d55784, d64992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6185 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d55794 q = 1) (hb : d65002 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55794, d65002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55794, d65002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6187 q ha hb
  have h3 (q : Pattern) (ha : d55795 q = 1) (hb : d65003 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55795, d65003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d55795, d65003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55805 q = 1) (hb : d65013 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55805, d65013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55805, d65013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6189 q ha hb
  have h5 (q : Pattern) (ha : d55806 q = 1) (hb : d65014 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55806, d65014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55806, d65014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55807 q = 1) (hb : d65015 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55807, d65015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55807, d65015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d55817 q = 1) (hb : d65025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55817, d65025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55817, d65025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6191 q ha hb
  have h8 (q : Pattern) (ha : d55818 q = 1) (hb : d65026 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55818, d65026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55818, d65026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d55819 q = 1) (hb : d65027 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55819, d65027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55819, d65027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d55820 q = 1) (hb : d65028 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d55820, d65028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55820, d65028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55830 q = 1) (hb : d65038 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55830, d65038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55830, d65038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6193 q ha hb
  have h12 (q : Pattern) (ha : d55831 q = 1) (hb : d65039 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55831, d65039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55831, d65039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d55832 q = 1) (hb : d65040 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55832, d65040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55832, d65040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d55833 q = 1) (hb : d65041 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d55833, d65041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55833, d65041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d55834 q = 1) (hb : d65042 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d55834, d65042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d55834, d65042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d55835 q = 1) (hb : d65043 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d55835, d65043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d55835, d65043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro6195 (p : Pattern) (ha : d55841 p = 1) (hb : d65049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55836 q = 1) (hb : d65044 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d55836, d65044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6194 q ha hb
    | true =>
      simp only [d55836, d65044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55837 q = 1) (hb : d65045 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d55837, d65045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55837, d65045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55838 q = 1) (hb : d65046 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d55838, d65046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55838, d65046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55839 q = 1) (hb : d65047 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d55839, d65047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55839, d65047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55840 q = 1) (hb : d65048 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d55840, d65048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55840, d65048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55841 q = 1) (hb : d65049 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d55841, d65049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55841, d65049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6196 (p : Pattern) (ha : d55847 p = 1) (hb : d65055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55842 q = 1) (hb : d65050 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d55842, d65050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6195 q ha hb
    | true =>
      simp only [d55842, d65050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55843 q = 1) (hb : d65051 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d55843, d65051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55843, d65051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55844 q = 1) (hb : d65052 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d55844, d65052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55844, d65052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55845 q = 1) (hb : d65053 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d55845, d65053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55845, d65053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55846 q = 1) (hb : d65054 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d55846, d65054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55846, d65054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55847 q = 1) (hb : d65055 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d55847, d65055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55847, d65055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6197 (p : Pattern) (ha : d55853 p = 1) (hb : d65061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55848 q = 1) (hb : d65056 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d55848, d65056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6196 q ha hb
    | true =>
      simp only [d55848, d65056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55849 q = 1) (hb : d65057 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d55849, d65057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55849, d65057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55850 q = 1) (hb : d65058 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d55850, d65058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55850, d65058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55851 q = 1) (hb : d65059 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d55851, d65059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55851, d65059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55852 q = 1) (hb : d65060 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d55852, d65060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55852, d65060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55853 q = 1) (hb : d65061 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d55853, d65061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55853, d65061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6198 (p : Pattern) (ha : d55859 p = 1) (hb : d65067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55854 q = 1) (hb : d65062 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d55854, d65062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6197 q ha hb
    | true =>
      simp only [d55854, d65062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55855 q = 1) (hb : d65063 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d55855, d65063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55855, d65063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55856 q = 1) (hb : d65064 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d55856, d65064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55856, d65064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55857 q = 1) (hb : d65065 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d55857, d65065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55857, d65065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55858 q = 1) (hb : d65066 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d55858, d65066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55858, d65066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55859 q = 1) (hb : d65067 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d55859, d65067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55859, d65067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6199 (p : Pattern) (ha : d55865 p = 1) (hb : d65073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55860 q = 1) (hb : d65068 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d55860, d65068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6198 q ha hb
    | true =>
      simp only [d55860, d65068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55861 q = 1) (hb : d65069 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d55861, d65069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55861, d65069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55862 q = 1) (hb : d65070 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d55862, d65070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55862, d65070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55863 q = 1) (hb : d65071 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d55863, d65071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55863, d65071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55864 q = 1) (hb : d65072 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d55864, d65072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55864, d65072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55865 q = 1) (hb : d65073 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d55865, d65073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55865, d65073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6200 (p : Pattern) (ha : d55871 p = 1) (hb : d65079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55866 q = 1) (hb : d65074 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d55866, d65074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6199 q ha hb
    | true =>
      simp only [d55866, d65074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55867 q = 1) (hb : d65075 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d55867, d65075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55867, d65075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55868 q = 1) (hb : d65076 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d55868, d65076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55868, d65076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55869 q = 1) (hb : d65077 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d55869, d65077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55869, d65077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55870 q = 1) (hb : d65078 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d55870, d65078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55870, d65078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55871 q = 1) (hb : d65079 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d55871, d65079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55871, d65079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6201 (p : Pattern) (ha : d55877 p = 1) (hb : d65085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55872 q = 1) (hb : d65080 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d55872, d65080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6200 q ha hb
    | true =>
      simp only [d55872, d65080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55873 q = 1) (hb : d65081 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d55873, d65081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55873, d65081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55874 q = 1) (hb : d65082 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d55874, d65082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55874, d65082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55875 q = 1) (hb : d65083 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d55875, d65083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55875, d65083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55876 q = 1) (hb : d65084 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d55876, d65084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55876, d65084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55877 q = 1) (hb : d65085 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d55877, d65085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55877, d65085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6202 (p : Pattern) (ha : d62704 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62702 q = 1) (hb : d64964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62702, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62702, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62703 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62703, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62703, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62704 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6203 (p : Pattern) (ha : d62712 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62710 q = 1) (hb : d64964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62710, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62710, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62711 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62711, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62711, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62712 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6204 (p : Pattern) (ha : d62718 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62705 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6202 q ha hb
  have h2 (q : Pattern) (ha : d62706 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62707 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62708 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62709 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62713 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6203 q ha hb
  have h7 (q : Pattern) (ha : d62714 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62715 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62716 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62717 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62718 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6205 (p : Pattern) (ha : d62721 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62719 q = 1) (hb : d64964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62719, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62719, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62720 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62720, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62720, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62721 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6206 (p : Pattern) (ha : d62727 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62722 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6205 q ha hb
  have h2 (q : Pattern) (ha : d62723 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62724 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62725 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62726 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62727 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6207 (p : Pattern) (ha : d62731 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62729 q = 1) (hb : d64964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62729, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62729, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62730 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62730, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62730, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62731 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6208 (p : Pattern) (ha : d62737 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62732 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6207 q ha hb
  have h2 (q : Pattern) (ha : d62733 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62734 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62735 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62736 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62737 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6209 (p : Pattern) (ha : d62742 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62740 q = 1) (hb : d64964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62740, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62740, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62741 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62741, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62741, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62742 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6210 (p : Pattern) (ha : d62748 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62743 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6209 q ha hb
  have h2 (q : Pattern) (ha : d62744 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62745 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62746 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62747 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62748 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6211 (p : Pattern) (ha : d62754 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2597 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62752 q = 1) (hb : d64964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62752, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62752, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62753 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62753, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62753, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62754 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6212 (p : Pattern) (ha : d62760 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62755 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6211 q ha hb
  have h2 (q : Pattern) (ha : d62756 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62757 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62758 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62759 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62760 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6213 (p : Pattern) (ha : d62767 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2614 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62765 q = 1) (hb : d64964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62765, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62765, d64964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d62766 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62766, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62766, d64965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d62767 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6214 (p : Pattern) (ha : d62773 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62768 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6213 q ha hb
  have h2 (q : Pattern) (ha : d62769 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62770 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62771 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62772 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62773 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6215 (p : Pattern) (ha : d62779 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62728 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6204 q ha hb
    | true =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6206 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62738 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6208 q ha hb
  have h3 (q : Pattern) (ha : d62739 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62749 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6210 q ha hb
  have h5 (q : Pattern) (ha : d62750 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62751 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62761 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6212 q ha hb
  have h8 (q : Pattern) (ha : d62762 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62763 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62764 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62774 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6214 q ha hb
  have h12 (q : Pattern) (ha : d62775 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62776 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62777 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62778 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62779 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6216 (p : Pattern) (ha : d62785 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62780 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6215 q ha hb
    | true =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62781 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62782 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62783 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62784 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62785 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6217 (p : Pattern) (ha : d62791 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62786 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6216 q ha hb
    | true =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62787 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62788 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62789 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62790 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62791 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6218 (p : Pattern) (ha : d62797 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62792 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6217 q ha hb
    | true =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62793 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62794 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62795 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62796 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62797 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6219 (p : Pattern) (ha : d62803 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62798 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6218 q ha hb
    | true =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62799 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62800 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62801 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62802 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62803 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6220 (p : Pattern) (ha : d62809 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62804 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6219 q ha hb
    | true =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62805 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62806 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62807 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62808 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62809 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6221 (p : Pattern) (ha : d62815 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62810 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6220 q ha hb
    | true =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62811 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62812 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62813 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62814 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62815 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6222 (p : Pattern) (ha : d62821 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62816 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6221 q ha hb
    | true =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62817 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62818 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62819 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62820 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62821 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6223 (p : Pattern) (ha : d62376 p = 1) (hb : d62701 p = 1) : d62701 p = 1 := by
  have h0 (q : Pattern) (ha : d62376 q = 1) (hb : d62701 q = 1) : d62701 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro6224 (p : Pattern) (ha : d3503 p = 1) (hb : d54187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51900 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3498 q = 1) (hb : d51908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3498, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3498, d51908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5733 q ha hb
  have h3 (q : Pattern) (ha : d3499 q = 1) (hb : d51909 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3499, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3499, d51909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3500 q = 1) (hb : d51910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3500, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3500, d51910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3501 q = 1) (hb : d51911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3501, d51911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51916 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3502 q = 1) (hb : d51917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, d51917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3502, d51917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3503 q = 1) (hb : d54187 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, d54187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3503, d54187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro6225 (p : Pattern) (ha : d54192 p = 1) (hb : d62560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5735 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3508 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3508, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52013 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52030 q = 1) (hb : d62555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52030, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52030, d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5736 q ha hb
  have h8 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d52033 q = 1) (hb : d62556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52033, d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52034 q = 1) (hb : d62557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52034, d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52035 q = 1) (hb : d62558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d52043 q = 1) (hb : d62559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52043, d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d54192 q = 1) (hb : d62560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54192, d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54192, d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro6226 (p : Pattern) (ha : d54198 p = 1) (hb : d62572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52083 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5738 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3521 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3521, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52143 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52162 q = 1) (hb : d62567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52162, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52162, d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5740 q ha hb
  have h8 (q : Pattern) (ha : d3524 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3524, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5739 q ha hb
    | true =>
      simp only [d3524, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5735 q ha hb
  have h9 (q : Pattern) (ha : d52165 q = 1) (hb : d62568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52165, d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52165, d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52166 q = 1) (hb : d62569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52166, d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52167 q = 1) (hb : d62570 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52167, d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d52177 q = 1) (hb : d62571 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52177, d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d54198 q = 1) (hb : d62572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54198, d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54198, d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro6227 (p : Pattern) (ha : d54204 p = 1) (hb : d62578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3504 q = 1) (hb : d54188 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, d54188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3504, d54188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6224 q ha hb
  have h2 (q : Pattern) (ha : d3505 q = 1) (hb : d54189 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, d54189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3505, d54189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3506 q = 1) (hb : d54190 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, d54190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3506, d54190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3507 q = 1) (hb : d54191 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, d54191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3507, d54191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54193 q = 1) (hb : d62561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54193, d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54193, d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6225 q ha hb
  have h6 (q : Pattern) (ha : d54194 q = 1) (hb : d62562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54194, d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54194, d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54195 q = 1) (hb : d62563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54195, d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54195, d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54196 q = 1) (hb : d62564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54196, d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54196, d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54197 q = 1) (hb : d62565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54197, d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d54197, d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54199 q = 1) (hb : d62573 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54199, d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54199, d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6226 q ha hb
  have h11 (q : Pattern) (ha : d54200 q = 1) (hb : d62574 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54200, d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54200, d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54201 q = 1) (hb : d62575 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54201, d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54201, d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54202 q = 1) (hb : d62576 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54202, d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54202, d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54203 q = 1) (hb : d62577 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54203, d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54203, d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54204 q = 1) (hb : d62578 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54204, d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54204, d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6228 (p : Pattern) (ha : d54205 p = 1) (hb : d62585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52244 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5743 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3536 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3536, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52315 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52336 q = 1) (hb : d62580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52336, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52336, d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5746 q ha hb
  have h8 (q : Pattern) (ha : d3540 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3540, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5744 q ha hb
    | true =>
      simp only [d3540, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5745 q ha hb
  have h9 (q : Pattern) (ha : d52350 q = 1) (hb : d62581 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52350, d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52350, d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52351 q = 1) (hb : d62582 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52351, d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52352 q = 1) (hb : d62583 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52352, d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d52362 q = 1) (hb : d62584 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52362, d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d54205 q = 1) (hb : d62585 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54205, d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54205, d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro6229 (p : Pattern) (ha : d54211 p = 1) (hb : d62591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54206 q = 1) (hb : d62586 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54206, d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54206, d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6228 q ha hb
  have h2 (q : Pattern) (ha : d54207 q = 1) (hb : d62587 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54207, d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54207, d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54208 q = 1) (hb : d62588 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54208, d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54208, d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54209 q = 1) (hb : d62589 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54209, d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54209, d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54210 q = 1) (hb : d62590 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54210, d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54210, d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54211 q = 1) (hb : d62591 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54211, d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54211, d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6230 (p : Pattern) (ha : d54213 p = 1) (hb : d62599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52466 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5749 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3553 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3553, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52536 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52557 q = 1) (hb : d62594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52557, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52557, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5752 q ha hb
  have h8 (q : Pattern) (ha : d3557 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3557, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5750 q ha hb
    | true =>
      simp only [d3557, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5751 q ha hb
  have h9 (q : Pattern) (ha : d52571 q = 1) (hb : d62595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52571, d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52571, d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52572 q = 1) (hb : d62596 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52572, d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52573 q = 1) (hb : d62597 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52573, d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d52583 q = 1) (hb : d62598 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52583, d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d54213 q = 1) (hb : d62599 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54213, d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54213, d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro6231 (p : Pattern) (ha : d54219 p = 1) (hb : d62605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54214 q = 1) (hb : d62600 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54214, d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54214, d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6230 q ha hb
  have h2 (q : Pattern) (ha : d54215 q = 1) (hb : d62601 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54215, d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54215, d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54216 q = 1) (hb : d62602 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54216, d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54216, d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54217 q = 1) (hb : d62603 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54217, d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54217, d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54218 q = 1) (hb : d62604 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54218, d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54218, d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54219 q = 1) (hb : d62605 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54219, d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54219, d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6232 (p : Pattern) (ha : d54222 p = 1) (hb : d62614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52749 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5755 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3571 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3571, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52816 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52837 q = 1) (hb : d62609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52837, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52837, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5758 q ha hb
  have h8 (q : Pattern) (ha : d3575 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3575, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5756 q ha hb
    | true =>
      simp only [d3575, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5757 q ha hb
  have h9 (q : Pattern) (ha : d52851 q = 1) (hb : d62610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52851, d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52851, d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52852 q = 1) (hb : d62611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52852, d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52853 q = 1) (hb : d62612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52853, d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d52863 q = 1) (hb : d62613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52863, d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d54222 q = 1) (hb : d62614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54222, d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54222, d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro6233 (p : Pattern) (ha : d54228 p = 1) (hb : d62620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54223 q = 1) (hb : d62615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54223, d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54223, d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6232 q ha hb
  have h2 (q : Pattern) (ha : d54224 q = 1) (hb : d62616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54224, d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54224, d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54225 q = 1) (hb : d62617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54225, d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54225, d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54226 q = 1) (hb : d62618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54226, d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54226, d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54227 q = 1) (hb : d62619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54227, d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54227, d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54228 q = 1) (hb : d62620 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54228, d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54228, d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6234 (p : Pattern) (ha : d54232 p = 1) (hb : d62630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5761 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3590 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3590, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53131 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53152 q = 1) (hb : d62625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53152, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53152, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5764 q ha hb
  have h8 (q : Pattern) (ha : d3594 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3594, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5762 q ha hb
    | true =>
      simp only [d3594, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5763 q ha hb
  have h9 (q : Pattern) (ha : d53166 q = 1) (hb : d62626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53166, d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53166, d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53167 q = 1) (hb : d62627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53167, d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d53168 q = 1) (hb : d62628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53168, d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d53178 q = 1) (hb : d62629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53178, d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d54232 q = 1) (hb : d62630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54232, d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54232, d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro6235 (p : Pattern) (ha : d54238 p = 1) (hb : d62636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54233 q = 1) (hb : d62631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54233, d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54233, d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6234 q ha hb
  have h2 (q : Pattern) (ha : d54234 q = 1) (hb : d62632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54234, d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54234, d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54235 q = 1) (hb : d62633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54235, d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54235, d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54236 q = 1) (hb : d62634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54236, d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54236, d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54237 q = 1) (hb : d62635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54237, d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54237, d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54238 q = 1) (hb : d62636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54238, d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54238, d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6236 (p : Pattern) (ha : d54243 p = 1) (hb : d62647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5767 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3610 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53448 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53469 q = 1) (hb : d62642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53469, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53469, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5770 q ha hb
  have h8 (q : Pattern) (ha : d3614 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3614, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5768 q ha hb
    | true =>
      simp only [d3614, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5769 q ha hb
  have h9 (q : Pattern) (ha : d53483 q = 1) (hb : d62643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53483, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53483, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53484 q = 1) (hb : d62644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53484, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d53485 q = 1) (hb : d62645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53485, d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d53495 q = 1) (hb : d62646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53495, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d54243 q = 1) (hb : d62647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54243, d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d54243, d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h14 p ha hb
theorem andIntro6237 (p : Pattern) (ha : d54249 p = 1) (hb : d62653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54244 q = 1) (hb : d62648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54244, d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54244, d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6236 q ha hb
  have h2 (q : Pattern) (ha : d54245 q = 1) (hb : d62649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54245, d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54245, d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54246 q = 1) (hb : d62650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54246, d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54246, d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54247 q = 1) (hb : d62651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54247, d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54247, d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54248 q = 1) (hb : d62652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54248, d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54248, d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54249 q = 1) (hb : d62653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54249, d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54249, d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6238 (p : Pattern) (ha : d54255 p = 1) (hb : d62659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54212 q = 1) (hb : d62592 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54212, d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6227 q ha hb
    | true =>
      simp only [d54212, d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6229 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54220 q = 1) (hb : d62606 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54220, d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54220, d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6231 q ha hb
  have h3 (q : Pattern) (ha : d54221 q = 1) (hb : d62607 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54221, d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54221, d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54229 q = 1) (hb : d62621 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54229, d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54229, d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6233 q ha hb
  have h5 (q : Pattern) (ha : d54230 q = 1) (hb : d62622 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54230, d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54230, d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54231 q = 1) (hb : d62623 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54231, d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54231, d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54239 q = 1) (hb : d62637 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54239, d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54239, d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6235 q ha hb
  have h8 (q : Pattern) (ha : d54240 q = 1) (hb : d62638 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54240, d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54240, d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54241 q = 1) (hb : d62639 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54241, d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54241, d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54242 q = 1) (hb : d62640 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54242, d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54242, d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54250 q = 1) (hb : d62654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54250, d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54250, d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6237 q ha hb
  have h12 (q : Pattern) (ha : d54251 q = 1) (hb : d62655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54251, d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54251, d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54252 q = 1) (hb : d62656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54252, d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54252, d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54253 q = 1) (hb : d62657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54253, d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54253, d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54254 q = 1) (hb : d62658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54254, d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54254, d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54255 q = 1) (hb : d62659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54255, d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54255, d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro6239 (p : Pattern) (ha : d54261 p = 1) (hb : d62665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54256 q = 1) (hb : d62660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54256, d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6238 q ha hb
    | true =>
      simp only [d54256, d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54257 q = 1) (hb : d62661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54257, d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54257, d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54258 q = 1) (hb : d62662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54258, d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54258, d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54259 q = 1) (hb : d62663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54259, d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54259, d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54260 q = 1) (hb : d62664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54260, d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54260, d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54261 q = 1) (hb : d62665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54261, d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54261, d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6240 (p : Pattern) (ha : d54267 p = 1) (hb : d62671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54262 q = 1) (hb : d62666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54262, d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6239 q ha hb
    | true =>
      simp only [d54262, d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54263 q = 1) (hb : d62667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54263, d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54263, d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54264 q = 1) (hb : d62668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54264, d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54264, d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54265 q = 1) (hb : d62669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54265, d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54265, d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54266 q = 1) (hb : d62670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54266, d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54266, d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54267 q = 1) (hb : d62671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54267, d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54267, d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6241 (p : Pattern) (ha : d54273 p = 1) (hb : d62677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54268 q = 1) (hb : d62672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54268, d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6240 q ha hb
    | true =>
      simp only [d54268, d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54269 q = 1) (hb : d62673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54269, d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54269, d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54270 q = 1) (hb : d62674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54270, d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54270, d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54271 q = 1) (hb : d62675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54271, d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54271, d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54272 q = 1) (hb : d62676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54272, d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54272, d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54273 q = 1) (hb : d62677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54273, d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54273, d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6242 (p : Pattern) (ha : d54279 p = 1) (hb : d62683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54274 q = 1) (hb : d62678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54274, d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6241 q ha hb
    | true =>
      simp only [d54274, d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54275 q = 1) (hb : d62679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54275, d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54275, d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54276 q = 1) (hb : d62680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54276, d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54276, d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54277 q = 1) (hb : d62681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54277, d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54277, d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54278 q = 1) (hb : d62682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54278, d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54278, d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54279 q = 1) (hb : d62683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54279, d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54279, d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6243 (p : Pattern) (ha : d54285 p = 1) (hb : d62689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54280 q = 1) (hb : d62684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54280, d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6242 q ha hb
    | true =>
      simp only [d54280, d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54281 q = 1) (hb : d62685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54281, d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54281, d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54282 q = 1) (hb : d62686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54282, d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54282, d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54283 q = 1) (hb : d62687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54283, d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54283, d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54284 q = 1) (hb : d62688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54284, d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54284, d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54285 q = 1) (hb : d62689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54285, d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54285, d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6244 (p : Pattern) (ha : d54291 p = 1) (hb : d62695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54286 q = 1) (hb : d62690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54286, d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6243 q ha hb
    | true =>
      simp only [d54286, d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54287 q = 1) (hb : d62691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54287, d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54287, d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54288 q = 1) (hb : d62692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54288, d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54288, d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54289 q = 1) (hb : d62693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54289, d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54289, d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54290 q = 1) (hb : d62694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54290, d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54290, d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54291 q = 1) (hb : d62695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54291, d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54291, d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6245 (p : Pattern) (ha : d54297 p = 1) (hb : d62701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54292 q = 1) (hb : d62696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54292, d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6244 q ha hb
    | true =>
      simp only [d54292, d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54293 q = 1) (hb : d62697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54293, d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54293, d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54294 q = 1) (hb : d62698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54294, d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54294, d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54295 q = 1) (hb : d62699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54295, d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54295, d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54296 q = 1) (hb : d62700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54296, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54296, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54297 q = 1) (hb : d62701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54297, d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54297, d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro6246 (p : Pattern) (ha : d62376 p = 1) (hb : d62821 p = 1) : d62821 p = 1 := by
  have h0 (q : Pattern) (ha : d62376 q = 1) (hb : d62821 q = 1) : d62821 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro6247 (p : Pattern) (ha : d54192 p = 1) (hb : d62704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5782 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2527 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2527, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52035 q = 1) (hb : d62702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52035, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52043 q = 1) (hb : d62703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52043, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54192 q = 1) (hb : d62704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54192, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54192, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
theorem andIntro6248 (p : Pattern) (ha : d54198 p = 1) (hb : d62712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5784 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2539 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2539, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52167 q = 1) (hb : d62710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52167, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52177 q = 1) (hb : d62711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52177, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d54198 q = 1) (hb : d62712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54198, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d54198, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h10 p ha hb
theorem andIntro6249 (p : Pattern) (ha : d54204 p = 1) (hb : d62718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54191 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54193 q = 1) (hb : d62705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54193, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54193, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6247 q ha hb
  have h3 (q : Pattern) (ha : d54194 q = 1) (hb : d62706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54194, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54194, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54195 q = 1) (hb : d62707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54195, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54195, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54196 q = 1) (hb : d62708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54196, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54196, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54197 q = 1) (hb : d62709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54197, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54197, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54199 q = 1) (hb : d62713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54199, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54199, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6248 q ha hb
  have h8 (q : Pattern) (ha : d54200 q = 1) (hb : d62714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54200, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54200, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54201 q = 1) (hb : d62715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54201, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54201, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54202 q = 1) (hb : d62716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54202, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54202, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54203 q = 1) (hb : d62717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54203, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54203, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54204 q = 1) (hb : d62718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54204, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54204, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
end NetHack.Soko22Hazard87
