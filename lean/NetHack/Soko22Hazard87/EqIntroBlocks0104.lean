import NetHack.Soko22Hazard87.EqIntroBlocks0103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro26000 (p : Pattern) (selected : d254658 p = 0) : d256503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254629 q = 0) : d256474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254629, d256474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254629, d256474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25941 q selected
  have h2 (q : Pattern) (selected : d254327 q = 0) : d256261 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254327, d256261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25941 q selected
    | true =>
      simp only [d254327, d256261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254630 q = 0) : d256475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254630, d256475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254630, d256475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254328 q = 0) : d256262 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254328, d256262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254328, d256262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254631 q = 0) : d256476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254631, d256476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254631, d256476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254632 q = 0) : d256477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254632, d256477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254632, d256477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254643 q = 0) : d256488 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254643, d256488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254643, d256488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254658 q = 0) : d256503 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254658, d256503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254658, d256503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26001 (p : Pattern) (selected : d254664 p = 0) : d256509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254635 q = 0) : d256480 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254635, d256480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25996 q selected
    | true =>
      simp only [d254635, d256480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25997 q selected
  have h2 (q : Pattern) (selected : d254636 q = 0) : d256481 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254636, d256481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254636, d256481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254637 q = 0) : d256482 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254637, d256482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254637, d256482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254645 q = 0) : d256490 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254645, d256490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25997 q selected
    | true =>
      simp only [d254645, d256490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25998 q selected
  have h5 (q : Pattern) (selected : d254646 q = 0) : d256491 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254646, d256491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254646, d256491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254647 q = 0) : d256492 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254647, d256492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254647, d256492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254648 q = 0) : d256493 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254648, d256493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254648, d256493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254655 q = 0) : d256500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254655, d256500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25997 q selected
    | true =>
      simp only [d254655, d256500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25999 q selected
  have h9 (q : Pattern) (selected : d254656 q = 0) : d256501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254656, d256501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254656, d256501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254657 q = 0) : d256502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254657, d256502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254657, d256502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254659 q = 0) : d256504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254659, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25999 q selected
    | true =>
      simp only [d254659, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26000 q selected
  have h12 (q : Pattern) (selected : d254660 q = 0) : d256505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254660, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254660, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254661 q = 0) : d256506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254661, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254661, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254662 q = 0) : d256507 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254662, d256507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254662, d256507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d254663 q = 0) : d256508 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254663, d256508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254663, d256508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254664 q = 0) : d256509 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254664, d256509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254664, d256509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro26002 (p : Pattern) (selected : d254669 p = 0) : d256514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254655 q = 0) : d256500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254655, d256500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25997 q selected
    | true =>
      simp only [d254655, d256500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25999 q selected
  have h2 (q : Pattern) (selected : d254656 q = 0) : d256501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254656, d256501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254656, d256501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254657 q = 0) : d256502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254657, d256502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254657, d256502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254659 q = 0) : d256504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254659, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25999 q selected
    | true =>
      simp only [d254659, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26000 q selected
  have h5 (q : Pattern) (selected : d254660 q = 0) : d256505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254660, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254660, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254661 q = 0) : d256506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254661, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254661, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254662 q = 0) : d256507 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254662, d256507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254662, d256507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254667 q = 0) : d256512 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254667, d256512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254667, d256512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254668 q = 0) : d256513 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254668, d256513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254668, d256513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254669 q = 0) : d256514 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254669, d256514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254669, d256514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26003 (p : Pattern) (selected : d254675 p = 0) : d256520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254665 q = 0) : d256510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254665, d256510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26001 q selected
    | true =>
      simp only [d254665, d256510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254666 q = 0) : d256511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254666, d256511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254666, d256511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254670 q = 0) : d256515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254670, d256515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26002 q selected
    | true =>
      simp only [d254670, d256515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254671 q = 0) : d256516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254671, d256516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254671, d256516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254672 q = 0) : d256517 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254672, d256517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254672, d256517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254673 q = 0) : d256518 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254673, d256518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254673, d256518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254674 q = 0) : d256519 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254674, d256519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254674, d256519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254675 q = 0) : d256520 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254675, d256520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254675, d256520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26004 (p : Pattern) (selected : d254677 p = 0) : d256522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254659 q = 0) : d256504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254659, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25999 q selected
    | true =>
      simp only [d254659, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26000 q selected
  have h2 (q : Pattern) (selected : d254660 q = 0) : d256505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254660, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254660, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254661 q = 0) : d256506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254661, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254661, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254667 q = 0) : d256512 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254667, d256512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254667, d256512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254676 q = 0) : d256521 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254676, d256521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254676, d256521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254677 q = 0) : d256522 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254677, d256522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254677, d256522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26005 (p : Pattern) (selected : d254683 p = 0) : d256528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254670 q = 0) : d256515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254670, d256515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26002 q selected
    | true =>
      simp only [d254670, d256515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254671 q = 0) : d256516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254671, d256516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254671, d256516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254678 q = 0) : d256523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254678, d256523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26004 q selected
    | true =>
      simp only [d254678, d256523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254679 q = 0) : d256524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254679, d256524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254679, d256524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254680 q = 0) : d256525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254680, d256525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254680, d256525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254681 q = 0) : d256526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254681, d256526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254681, d256526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254682 q = 0) : d256527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254682, d256527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254682, d256527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254683 q = 0) : d256528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254683, d256528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254683, d256528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26006 (p : Pattern) (selected : d254703 p = 0) : d256479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254685 q = 0) : d256465 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254685, d256465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254685, d256465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25969 q selected
  have h2 (q : Pattern) (selected : d254474 q = 0) : d256238 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254474, d256238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25969 q selected
    | true =>
      simp only [d254474, d256238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254686 q = 0) : d256466 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254686, d256466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254686, d256466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254475 q = 0) : d256239 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254475, d256239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254475, d256239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254687 q = 0) : d256467 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254687, d256467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254687, d256467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254688 q = 0) : d256468 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254688, d256468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254688, d256468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254689 q = 0) : d256469 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254689, d256469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254689, d256469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25970 q selected
  have h8 (q : Pattern) (selected : d254484 q = 0) : d256248 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254484, d256248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25970 q selected
    | true =>
      simp only [d254484, d256248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254690 q = 0) : d256470 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254690, d256470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254690, d256470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254485 q = 0) : d256249 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254485, d256249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254485, d256249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254691 q = 0) : d256471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254691, d256471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254691, d256471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254692 q = 0) : d256472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254692, d256472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254692, d256472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254693 q = 0) : d256473 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254693, d256473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254693, d256473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254694 q = 0) : d256459 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254694, d256459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254694, d256459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25971 q selected
  have h15 (q : Pattern) (selected : d254492 q = 0) : d256254 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254492, d256254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25971 q selected
    | true =>
      simp only [d254492, d256254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254695 q = 0) : d256460 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254695, d256460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254695, d256460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254493 q = 0) : d256255 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254493, d256255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254493, d256255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254696 q = 0) : d256461 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254696, d256461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254696, d256461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254697 q = 0) : d256462 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254697, d256462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d254697, d256462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d254698 q = 0) : d256474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254698, d256474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254698, d256474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25972 q selected
  have h21 (q : Pattern) (selected : d254499 q = 0) : d256261 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, d256261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25972 q selected
    | true =>
      simp only [d254499, d256261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d254699 q = 0) : d256475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254699, d256475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d254699, d256475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d254500 q = 0) : d256262 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, d256262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d254500, d256262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d254700 q = 0) : d256476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254700, d256476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d254700, d256476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d254701 q = 0) : d256477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254701, d256477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d254701, d256477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d254702 q = 0) : d256478 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254702, d256478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d254702, d256478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d254703 q = 0) : d256479 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254703, d256479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254703, d256479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro26007 (p : Pattern) (selected : d254710 p = 0) : d256499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254704 q = 0) : d256494 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254704, d256494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254704, d256494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25974 q selected
  have h2 (q : Pattern) (selected : d254506 q = 0) : d256268 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254506, d256268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25974 q selected
    | true =>
      simp only [d254506, d256268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254705 q = 0) : d256495 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254705, d256495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254705, d256495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254507 q = 0) : d256269 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254507, d256269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254507, d256269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254706 q = 0) : d256496 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254706, d256496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254706, d256496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254707 q = 0) : d256497 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254707, d256497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254707, d256497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254698 q = 0) : d256474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254698, d256474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254698, d256474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25972 q selected
  have h8 (q : Pattern) (selected : d254499 q = 0) : d256261 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, d256261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25972 q selected
    | true =>
      simp only [d254499, d256261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254699 q = 0) : d256475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254699, d256475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254699, d256475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254500 q = 0) : d256262 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, d256262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254500, d256262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254700 q = 0) : d256476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254700, d256476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254700, d256476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254701 q = 0) : d256477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254701, d256477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254701, d256477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254708 q = 0) : d256498 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254708, d256498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254708, d256498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254709 q = 0) : d256488 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254709, d256488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254709, d256488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254710 q = 0) : d256499 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254710, d256499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254710, d256499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26008 (p : Pattern) (selected : d254714 p = 0) : d256503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254698 q = 0) : d256474 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254698, d256474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254698, d256474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25972 q selected
  have h2 (q : Pattern) (selected : d254499 q = 0) : d256261 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, d256261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25972 q selected
    | true =>
      simp only [d254499, d256261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254699 q = 0) : d256475 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254699, d256475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254699, d256475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254500 q = 0) : d256262 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, d256262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254500, d256262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254700 q = 0) : d256476 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254700, d256476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254700, d256476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254701 q = 0) : d256477 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254701, d256477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254701, d256477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254709 q = 0) : d256488 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254709, d256488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254709, d256488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254714 q = 0) : d256503 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254714, d256503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254714, d256503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26009 (p : Pattern) (selected : d254721 p = 0) : d256514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254711 q = 0) : d256500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254711, d256500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26006 q selected
    | true =>
      simp only [d254711, d256500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26007 q selected
  have h2 (q : Pattern) (selected : d254712 q = 0) : d256501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254712, d256501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254712, d256501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254713 q = 0) : d256502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254713, d256502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254713, d256502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254715 q = 0) : d256504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254715, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26007 q selected
    | true =>
      simp only [d254715, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26008 q selected
  have h5 (q : Pattern) (selected : d254716 q = 0) : d256505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254716, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254716, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254717 q = 0) : d256506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254717, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254717, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254718 q = 0) : d256507 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254718, d256507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254718, d256507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254719 q = 0) : d256512 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254719, d256512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254719, d256512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254720 q = 0) : d256513 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254720, d256513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254720, d256513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254721 q = 0) : d256514 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254721, d256514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254721, d256514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26010 (p : Pattern) (selected : d254725 p = 0) : d256522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254715 q = 0) : d256504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254715, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26007 q selected
    | true =>
      simp only [d254715, d256504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26008 q selected
  have h2 (q : Pattern) (selected : d254716 q = 0) : d256505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254716, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254716, d256505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254717 q = 0) : d256506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254717, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254717, d256506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254719 q = 0) : d256512 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254719, d256512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254719, d256512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254724 q = 0) : d256521 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254724, d256521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254724, d256521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254725 q = 0) : d256522 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254725, d256522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254725, d256522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26011 (p : Pattern) (selected : d254731 p = 0) : d256528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254722 q = 0) : d256515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254722, d256515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26009 q selected
    | true =>
      simp only [d254722, d256515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254723 q = 0) : d256516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254723, d256516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254723, d256516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254726 q = 0) : d256523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254726, d256523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26010 q selected
    | true =>
      simp only [d254726, d256523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254727 q = 0) : d256524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254727, d256524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254727, d256524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254728 q = 0) : d256525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254728, d256525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254728, d256525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254729 q = 0) : d256526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254729, d256526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254729, d256526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254730 q = 0) : d256527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254730, d256527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254730, d256527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254731 q = 0) : d256528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254731, d256528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254731, d256528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26012 (p : Pattern) (selected : d254735 p = 0) : d256533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254726 q = 0) : d256523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254726, d256523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26010 q selected
    | true =>
      simp only [d254726, d256523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254727 q = 0) : d256524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254727, d256524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254727, d256524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254732 q = 0) : d256530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254732, d256530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254732, d256530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254733 q = 0) : d256531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254733, d256531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254733, d256531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254734 q = 0) : d256532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254734, d256532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254734, d256532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254735 q = 0) : d256533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254735, d256533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254735, d256533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26013 (p : Pattern) (selected : d254741 p = 0) : d256539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254670 q = 0) : d256515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254670, d256515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26002 q selected
    | true =>
      simp only [d254670, d256515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254671 q = 0) : d256516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254671, d256516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254671, d256516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254738 q = 0) : d256536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254738, d256536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254738, d256536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254739 q = 0) : d256537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254739, d256537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254739, d256537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254740 q = 0) : d256538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254740, d256538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254740, d256538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254741 q = 0) : d256539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254741, d256539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254741, d256539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26014 (p : Pattern) (selected : d254747 p = 0) : d256545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254684 q = 0) : d256529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254684, d256529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26003 q selected
    | true =>
      simp only [d254684, d256529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26005 q selected
  have h2 (q : Pattern) (selected : d254736 q = 0) : d256534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254736, d256534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26011 q selected
    | true =>
      simp only [d254736, d256534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26012 q selected
  have h3 (q : Pattern) (selected : d254737 q = 0) : d256535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254737, d256535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254737, d256535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254742 q = 0) : d256540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254742, d256540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26013 q selected
    | true =>
      simp only [d254742, d256540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254743 q = 0) : d256541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254743, d256541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254743, d256541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254744 q = 0) : d256542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254744, d256542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254744, d256542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254745 q = 0) : d256543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254745, d256543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254745, d256543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254746 q = 0) : d256544 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254746, d256544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254746, d256544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254747 q = 0) : d256545 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254747, d256545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254747, d256545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro26015 (p : Pattern) (selected : d254752 p = 0) : d256533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254678 q = 0) : d256523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254678, d256523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26004 q selected
    | true =>
      simp only [d254678, d256523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254679 q = 0) : d256524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254679, d256524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254679, d256524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254749 q = 0) : d256530 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254749, d256530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254749, d256530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254750 q = 0) : d256531 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254750, d256531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254750, d256531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254751 q = 0) : d256532 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254751, d256532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254751, d256532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254752 q = 0) : d256533 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254752, d256533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254752, d256533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26016 (p : Pattern) (selected : d254758 p = 0) : d256552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254753 q = 0) : d256547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254753, d256547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26015 q selected
    | true =>
      simp only [d254753, d256547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254754 q = 0) : d256548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254754, d256548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254754, d256548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254755 q = 0) : d256549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254755, d256549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254755, d256549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254756 q = 0) : d256550 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254756, d256550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254756, d256550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254757 q = 0) : d256551 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254757, d256551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254757, d256551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254758 q = 0) : d256552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254758, d256552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254758, d256552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26017 (p : Pattern) (selected : d254764 p = 0) : d256558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254372 q = 0) : d256306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254372, d256306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254372, d256306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25950 q selected
  have h2 (q : Pattern) (selected : d254373 q = 0) : d256307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254373, d256307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254373, d256307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254382 q = 0) : d256316 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254382, d256316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25950 q selected
    | true =>
      simp only [d254382, d256316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25953 q selected
  have h4 (q : Pattern) (selected : d254383 q = 0) : d256317 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254383, d256317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254383, d256317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254384 q = 0) : d256318 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d254384, d256318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254384, d256318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254574 q = 0) : d256419 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254574, d256419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25982 q selected
    | true =>
      simp only [d254574, d256419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25991 q selected
  have h7 (q : Pattern) (selected : d254587 q = 0) : d256432 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254587, d256432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25992 q selected
    | true =>
      simp only [d254587, d256432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25993 q selected
  have h8 (q : Pattern) (selected : d254588 q = 0) : d256433 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254588, d256433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254588, d256433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254589 q = 0) : d256434 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d254589, d256434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254589, d256434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254590 q = 0) : d256435 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d254590, d256435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254590, d256435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254594 q = 0) : d256439 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254594, d256439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254594, d256439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25994 q selected
  have h12 (q : Pattern) (selected : d254596 q = 0) : d256441 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254596, d256441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254596, d256441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25995 q selected
  have h13 (q : Pattern) (selected : d254597 q = 0) : d256442 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254597, d256442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254597, d256442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254598 q = 0) : d256443 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d254598, d256443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254598, d256443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254599 q = 0) : d256444 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d254599, d256444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254599, d256444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254600 q = 0) : d256445 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d254600, d256445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254600, d256445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254748 q = 0) : d256546 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254748, d256546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254748, d256546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26014 q selected
  have h18 (q : Pattern) (selected : d254759 q = 0) : d256553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254759, d256553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254759, d256553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26016 q selected
  have h19 (q : Pattern) (selected : d254760 q = 0) : d256554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254760, d256554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d254760, d256554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d254761 q = 0) : d256555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d254761, d256555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d254761, d256555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d254762 q = 0) : d256556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d254762, d256556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d254762, d256556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d254763 q = 0) : d256557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d254763, d256557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d254763, d256557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d254764 q = 0) : d256558 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d254764, d256558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254764, d256558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro26018 (p : Pattern) (selected : d254770 p = 0) : d256564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254765 q = 0) : d256559 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d254765, d256559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254765, d256559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26017 q selected
  have h2 (q : Pattern) (selected : d254766 q = 0) : d256560 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d254766, d256560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254766, d256560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254767 q = 0) : d256561 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d254767, d256561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254767, d256561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254768 q = 0) : d256562 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d254768, d256562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254768, d256562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254769 q = 0) : d256563 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d254769, d256563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254769, d256563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254770 q = 0) : d256564 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d254770, d256564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254770, d256564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26019 (p : Pattern) (selected : d254779 p = 0) : d256573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254025 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25887 q selected
    | true =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254026 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254402 q = 0) : d256336 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254402, d256336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254402, d256336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254403 q = 0) : d256337 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254403, d256337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254403, d256337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254404 q = 0) : d256338 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254404, d256338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254404, d256338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254774 q = 0) : d256568 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254774, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254774, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
  have h7 (q : Pattern) (selected : d254775 q = 0) : d256569 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254775, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254775, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254776 q = 0) : d256570 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254776, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254776, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254033 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
    | true =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254034 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254405 q = 0) : d256339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254405, d256339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254405, d256339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254777 q = 0) : d256571 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254777, d256571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254777, d256571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254778 q = 0) : d256572 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254778, d256572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254778, d256572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d254779 q = 0) : d256573 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254779, d256573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254779, d256573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro26020 (p : Pattern) (selected : d254786 p = 0) : d256580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253615 q = 0) : d255724 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d253615, d255724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253615, d255724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254786 q = 0) : d256580 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d254786, d256580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254786, d256580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro26021 (p : Pattern) (selected : d254793 p = 0) : d256587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254025 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25887 q selected
    | true =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254026 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254774 q = 0) : d256568 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254774, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254774, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
  have h4 (q : Pattern) (selected : d254775 q = 0) : d256569 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254775, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254775, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254776 q = 0) : d256570 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254776, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254776, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254030 q = 0) : d256043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254030, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254030, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254031 q = 0) : d256044 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254031, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254031, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254033 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
    | true =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254034 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254035 q = 0) : d256048 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254035, d256048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254035, d256048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254784 q = 0) : d256578 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254784, d256578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254784, d256578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254785 q = 0) : d256579 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254785, d256579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254785, d256579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254787 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26020 q selected
  have h14 (q : Pattern) (selected : d254788 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25793 q selected
  have h15 (q : Pattern) (selected : d254789 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254790 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h17 (q : Pattern) (selected : d254791 q = 0) : d256585 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254791, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254791, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254792 q = 0) : d256586 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254792, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d254792, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d254793 q = 0) : d256587 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254793, d256587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254793, d256587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26022 (p : Pattern) (selected : d254802 p = 0) : d256596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254025 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25887 q selected
    | true =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254026 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254030 q = 0) : d256043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254030, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254030, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254031 q = 0) : d256044 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254031, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254031, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254799 q = 0) : d256593 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254799, d256593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254799, d256593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254800 q = 0) : d256594 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254800, d256594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254800, d256594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254801 q = 0) : d256595 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254801, d256595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254801, d256595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254787 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26020 q selected
  have h9 (q : Pattern) (selected : d254788 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25793 q selected
  have h10 (q : Pattern) (selected : d254789 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254033 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
    | true =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254034 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254790 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254791 q = 0) : d256585 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254791, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254791, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254792 q = 0) : d256586 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254792, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254792, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254802 q = 0) : d256596 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254802, d256596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254802, d256596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro26023 (p : Pattern) (selected : d254810 p = 0) : d256604 p = 1 := by
  have h0 (q : Pattern) (selected : d254787 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26020 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d254788 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25793 q selected
  have h3 (q : Pattern) (selected : d254789 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254033 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
    | true =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d254034 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d254790 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254807 q = 0) : d256601 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254807, d256601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254807, d256601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d254808 q = 0) : d256602 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254808, d256602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254808, d256602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254809 q = 0) : d256603 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254809, d256603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254809, d256603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d254810 q = 0) : d256604 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254810, d256604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254810, d256604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h10 p selected
theorem eqIntro26024 (p : Pattern) (selected : d254816 p = 0) : d256610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254780 q = 0) : d256574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254780, d256574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26019 q selected
    | true =>
      simp only [d254780, d256574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254781 q = 0) : d256575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254781, d256575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254781, d256575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254782 q = 0) : d256576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254782, d256576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254782, d256576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254783 q = 0) : d256577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254783, d256577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254783, d256577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254794 q = 0) : d256588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254794, d256588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26021 q selected
    | true =>
      simp only [d254794, d256588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254795 q = 0) : d256589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254795, d256589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254795, d256589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254796 q = 0) : d256590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254796, d256590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254796, d256590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254797 q = 0) : d256591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254797, d256591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254797, d256591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254798 q = 0) : d256592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254798, d256592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254798, d256592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254803 q = 0) : d256597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254803, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26022 q selected
    | true =>
      simp only [d254803, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254804 q = 0) : d256598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254804, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254804, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254805 q = 0) : d256599 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254805, d256599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254805, d256599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254806 q = 0) : d256600 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254806, d256600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254806, d256600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d254811 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
    | true =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254812 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254813 q = 0) : d256607 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254813, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254813, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254814 q = 0) : d256608 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254814, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254814, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254815 q = 0) : d256609 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254815, d256609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254815, d256609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254816 q = 0) : d256610 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254816, d256610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254816, d256610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26025 (p : Pattern) (selected : d254817 p = 0) : d256611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254025 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25887 q selected
    | true =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254026 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254774 q = 0) : d256568 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254774, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254774, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
  have h4 (q : Pattern) (selected : d254775 q = 0) : d256569 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254775, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254775, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254776 q = 0) : d256570 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254776, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254776, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254030 q = 0) : d256043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254030, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254030, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254031 q = 0) : d256044 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254031, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254031, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254033 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
    | true =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254034 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254035 q = 0) : d256048 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254035, d256048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254035, d256048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254784 q = 0) : d256578 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254784, d256578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254784, d256578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254785 q = 0) : d256579 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254785, d256579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254785, d256579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254787 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26020 q selected
  have h14 (q : Pattern) (selected : d254788 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25793 q selected
  have h15 (q : Pattern) (selected : d254789 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254790 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h17 (q : Pattern) (selected : d254807 q = 0) : d256601 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254807, d256601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254807, d256601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254808 q = 0) : d256602 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254808, d256602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254808, d256602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254809 q = 0) : d256603 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254809, d256603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d254809, d256603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d254817 q = 0) : d256611 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254817, d256611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254817, d256611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro26026 (p : Pattern) (selected : d254824 p = 0) : d256618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254818 q = 0) : d256612 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254818, d256612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26025 q selected
    | true =>
      simp only [d254818, d256612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254819 q = 0) : d256613 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254819, d256613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254819, d256613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254820 q = 0) : d256614 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254820, d256614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254820, d256614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254821 q = 0) : d256615 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254821, d256615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254821, d256615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254811 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
    | true =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254812 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254813 q = 0) : d256607 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254813, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254813, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254814 q = 0) : d256608 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254814, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254814, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254822 q = 0) : d256616 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254822, d256616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254822, d256616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254823 q = 0) : d256617 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254823, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254823, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254824 q = 0) : d256618 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254824, d256618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254824, d256618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26027 (p : Pattern) (selected : d254828 p = 0) : d256622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254811 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
    | true =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254812 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254813 q = 0) : d256607 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254813, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254813, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254814 q = 0) : d256608 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254814, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254814, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254823 q = 0) : d256617 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254823, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254823, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254828 q = 0) : d256622 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254828, d256622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254828, d256622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26028 (p : Pattern) (selected : d254835 p = 0) : d256629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254825 q = 0) : d256619 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254825, d256619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26024 q selected
    | true =>
      simp only [d254825, d256619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26026 q selected
  have h2 (q : Pattern) (selected : d254826 q = 0) : d256620 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254826, d256620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254826, d256620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254827 q = 0) : d256621 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254827, d256621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254827, d256621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254829 q = 0) : d256623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254829, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26026 q selected
    | true =>
      simp only [d254829, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26027 q selected
  have h5 (q : Pattern) (selected : d254830 q = 0) : d256624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254830, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254830, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254831 q = 0) : d256625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254831, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254831, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254832 q = 0) : d256626 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254832, d256626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254832, d256626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254833 q = 0) : d256627 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254833, d256627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254833, d256627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254834 q = 0) : d256628 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254834, d256628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254834, d256628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254835 q = 0) : d256629 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254835, d256629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254835, d256629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26029 (p : Pattern) (selected : d254839 p = 0) : d256633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254829 q = 0) : d256623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254829, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26026 q selected
    | true =>
      simp only [d254829, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26027 q selected
  have h2 (q : Pattern) (selected : d254830 q = 0) : d256624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254830, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254830, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254831 q = 0) : d256625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254831, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254831, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254833 q = 0) : d256627 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254833, d256627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254833, d256627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254838 q = 0) : d256632 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254838, d256632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254838, d256632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254839 q = 0) : d256633 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254839, d256633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254839, d256633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26030 (p : Pattern) (selected : d254845 p = 0) : d256639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254842 q = 0) : d256636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254843 q = 0) : d256637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254843, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254843, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254844 q = 0) : d256638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254844, d256638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254844, d256638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254845 q = 0) : d256639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254845, d256639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254845, d256639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26031 (p : Pattern) (selected : d254849 p = 0) : d256643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254846 q = 0) : d256640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254847 q = 0) : d256641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254847, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254847, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254848 q = 0) : d256642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254848, d256642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254848, d256642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254849 q = 0) : d256643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254849, d256643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254849, d256643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26032 (p : Pattern) (selected : d254855 p = 0) : d256649 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254850 q = 0) : d256644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254850, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26030 q selected
    | true =>
      simp only [d254850, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26031 q selected
  have h2 (q : Pattern) (selected : d254851 q = 0) : d256645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254851, d256645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254851, d256645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254852 q = 0) : d256646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254852, d256646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254852, d256646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254853 q = 0) : d256647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254853, d256647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254853, d256647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254854 q = 0) : d256648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254854, d256648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254854, d256648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254855 q = 0) : d256649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254855, d256649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254855, d256649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26033 (p : Pattern) (selected : d254858 p = 0) : d256652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254842 q = 0) : d256636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254843 q = 0) : d256637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254843, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254843, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254844 q = 0) : d256638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254844, d256638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254844, d256638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254858 q = 0) : d256652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254858, d256652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254858, d256652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26034 (p : Pattern) (selected : d254859 p = 0) : d256653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254846 q = 0) : d256640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254847 q = 0) : d256641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254847, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254847, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254848 q = 0) : d256642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254848, d256642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254848, d256642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254859 q = 0) : d256653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254859, d256653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254859, d256653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26035 (p : Pattern) (selected : d254865 p = 0) : d256659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254850 q = 0) : d256644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254850, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26030 q selected
    | true =>
      simp only [d254850, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26031 q selected
  have h2 (q : Pattern) (selected : d254851 q = 0) : d256645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254851, d256645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254851, d256645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254852 q = 0) : d256646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254852, d256646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254852, d256646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254853 q = 0) : d256647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254853, d256647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254853, d256647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254854 q = 0) : d256648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254854, d256648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254854, d256648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254860 q = 0) : d256654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254860, d256654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26033 q selected
    | true =>
      simp only [d254860, d256654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26034 q selected
  have h7 (q : Pattern) (selected : d254861 q = 0) : d256655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254861, d256655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254861, d256655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254862 q = 0) : d256656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254862, d256656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254862, d256656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254863 q = 0) : d256657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254863, d256657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254863, d256657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254864 q = 0) : d256658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254864, d256658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254864, d256658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254865 q = 0) : d256659 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254865, d256659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254865, d256659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26036 (p : Pattern) (selected : d254870 p = 0) : d256664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254842 q = 0) : d256636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254843 q = 0) : d256637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254843, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254843, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254869 q = 0) : d256663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254869, d256663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254869, d256663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254870 q = 0) : d256664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254870, d256664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254870, d256664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26037 (p : Pattern) (selected : d254872 p = 0) : d256666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254846 q = 0) : d256640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254847 q = 0) : d256641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254847, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254847, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254871 q = 0) : d256665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254871, d256665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254871, d256665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254872 q = 0) : d256666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254872, d256666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254872, d256666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26038 (p : Pattern) (selected : d254879 p = 0) : d256673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254842 q = 0) : d256636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254877 q = 0) : d256671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254877, d256671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254877, d256671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254878 q = 0) : d256672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254878, d256672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254878, d256672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254879 q = 0) : d256673 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254879, d256673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254879, d256673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26039 (p : Pattern) (selected : d254882 p = 0) : d256676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254846 q = 0) : d256640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254880 q = 0) : d256674 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254880, d256674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254880, d256674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254881 q = 0) : d256675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254881, d256675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254881, d256675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254882 q = 0) : d256676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254882, d256676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254882, d256676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26040 (p : Pattern) (selected : d254886 p = 0) : d256680 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254025 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25887 q selected
    | true =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254026 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254402 q = 0) : d256336 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254402, d256336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254402, d256336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254403 q = 0) : d256337 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254403, d256337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254403, d256337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254404 q = 0) : d256338 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254404, d256338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254404, d256338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254886 q = 0) : d256680 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254886, d256680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254886, d256680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26041 (p : Pattern) (selected : d254891 p = 0) : d256685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254025 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25887 q selected
    | true =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254026 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254402 q = 0) : d256336 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254402, d256336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254402, d256336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254403 q = 0) : d256337 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254403, d256337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254403, d256337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254404 q = 0) : d256338 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254404, d256338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254404, d256338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254030 q = 0) : d256043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254030, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254030, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254031 q = 0) : d256044 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254031, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254031, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254799 q = 0) : d256593 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254799, d256593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254799, d256593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254800 q = 0) : d256594 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254800, d256594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254800, d256594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254801 q = 0) : d256595 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254801, d256595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254801, d256595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254891 q = 0) : d256685 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254891, d256685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254891, d256685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26042 (p : Pattern) (selected : d254898 p = 0) : d256692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254887 q = 0) : d256681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254887, d256681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26040 q selected
    | true =>
      simp only [d254887, d256681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254888 q = 0) : d256682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254888, d256682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254888, d256682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254889 q = 0) : d256683 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254889, d256683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254889, d256683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254890 q = 0) : d256684 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254890, d256684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254890, d256684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254892 q = 0) : d256686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254892, d256686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26041 q selected
    | true =>
      simp only [d254892, d256686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254893 q = 0) : d256687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254893, d256687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254893, d256687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254894 q = 0) : d256688 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254894, d256688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254894, d256688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254895 q = 0) : d256689 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254895, d256689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254895, d256689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254896 q = 0) : d256690 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254896, d256690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254896, d256690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254803 q = 0) : d256597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254803, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26022 q selected
    | true =>
      simp only [d254803, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254804 q = 0) : d256598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254804, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254804, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254805 q = 0) : d256599 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254805, d256599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254805, d256599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254806 q = 0) : d256600 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254806, d256600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254806, d256600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d254897 q = 0) : d256691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254897, d256691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254897, d256691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d254898 q = 0) : d256692 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254898, d256692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254898, d256692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26043 (p : Pattern) (selected : d254904 p = 0) : d256698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254025 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25887 q selected
    | true =>
      simp only [d254025, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254026 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254026, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254774 q = 0) : d256568 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254774, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254774, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
  have h4 (q : Pattern) (selected : d254775 q = 0) : d256569 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254775, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254775, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254776 q = 0) : d256570 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254776, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254776, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254902 q = 0) : d256696 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254902, d256696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254902, d256696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254903 q = 0) : d256697 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254903, d256697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254903, d256697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254787 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25888 q selected
    | true =>
      simp only [d254787, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26020 q selected
  have h9 (q : Pattern) (selected : d254788 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254788, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25793 q selected
  have h10 (q : Pattern) (selected : d254789 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254789, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254033 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
    | true =>
      simp only [d254033, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254034 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254034, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254790 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254790, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254791 q = 0) : d256585 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254791, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254791, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254792 q = 0) : d256586 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254792, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254792, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254904 q = 0) : d256698 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254904, d256698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254904, d256698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro26044 (p : Pattern) (selected : d254910 p = 0) : d256704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254905 q = 0) : d256699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254905, d256699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26043 q selected
    | true =>
      simp only [d254905, d256699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254906 q = 0) : d256700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254906, d256700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254906, d256700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254907 q = 0) : d256701 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254907, d256701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254907, d256701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254908 q = 0) : d256702 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254908, d256702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254908, d256702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254811 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
    | true =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254812 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254813 q = 0) : d256607 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254813, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254813, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254814 q = 0) : d256608 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254814, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254814, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254909 q = 0) : d256703 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254909, d256703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254909, d256703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254823 q = 0) : d256617 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254823, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254823, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254910 q = 0) : d256704 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254910, d256704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254910, d256704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26045 (p : Pattern) (selected : d254916 p = 0) : d256710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254899 q = 0) : d256693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254899, d256693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26042 q selected
    | true =>
      simp only [d254899, d256693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26024 q selected
  have h2 (q : Pattern) (selected : d254900 q = 0) : d256694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254900, d256694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254900, d256694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254901 q = 0) : d256695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254901, d256695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254901, d256695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254911 q = 0) : d256705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254911, d256705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26024 q selected
    | true =>
      simp only [d254911, d256705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26044 q selected
  have h5 (q : Pattern) (selected : d254912 q = 0) : d256706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254912, d256706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254912, d256706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254913 q = 0) : d256707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254913, d256707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254913, d256707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254914 q = 0) : d256708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254914, d256708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254914, d256708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254825 q = 0) : d256619 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254825, d256619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26024 q selected
    | true =>
      simp only [d254825, d256619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26026 q selected
  have h9 (q : Pattern) (selected : d254826 q = 0) : d256620 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254826, d256620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254826, d256620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254827 q = 0) : d256621 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254827, d256621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254827, d256621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254829 q = 0) : d256623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254829, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26026 q selected
    | true =>
      simp only [d254829, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26027 q selected
  have h12 (q : Pattern) (selected : d254830 q = 0) : d256624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254830, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254830, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254831 q = 0) : d256625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254831, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254831, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254832 q = 0) : d256626 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254832, d256626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254832, d256626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d254915 q = 0) : d256709 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254915, d256709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254915, d256709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254916 q = 0) : d256710 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254916, d256710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254916, d256710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro26046 (p : Pattern) (selected : d254922 p = 0) : d256716 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254917 q = 0) : d256711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254917, d256711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26045 q selected
    | true =>
      simp only [d254917, d256711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254918 q = 0) : d256712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254918, d256712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254918, d256712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254919 q = 0) : d256713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254919, d256713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254919, d256713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254920 q = 0) : d256714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254920, d256714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254920, d256714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254921 q = 0) : d256715 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254921, d256715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254921, d256715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254922 q = 0) : d256716 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254922, d256716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254922, d256716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26047 (p : Pattern) (selected : d254933 p = 0) : d256573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254454 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254454, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25966 q selected
    | true =>
      simp only [d254454, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254455 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254455, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254455, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254924 q = 0) : d256336 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254924, d256336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254924, d256336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254925 q = 0) : d256337 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254925, d256337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254925, d256337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254926 q = 0) : d256338 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254926, d256338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254926, d256338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254927 q = 0) : d256568 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254927, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254927, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
  have h7 (q : Pattern) (selected : d254928 q = 0) : d256569 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254928, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254928, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254929 q = 0) : d256570 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254929, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254929, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254462 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
    | true =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254463 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254930 q = 0) : d256339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254930, d256339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254930, d256339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254931 q = 0) : d256571 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254931, d256571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254931, d256571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254932 q = 0) : d256572 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254932, d256572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254932, d256572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d254933 q = 0) : d256573 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254933, d256573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254933, d256573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro26048 (p : Pattern) (selected : d254940 p = 0) : d256580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d158 q = 0) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d159 q = 0) : d51866 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d159, d51866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253823 q = 0) : d255724 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d253823, d255724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253823, d255724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254940 q = 0) : d256580 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d254940, d256580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254940, d256580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro26049 (p : Pattern) (selected : d254947 p = 0) : d256587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254454 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254454, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25966 q selected
    | true =>
      simp only [d254454, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254455 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254455, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254455, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254927 q = 0) : d256568 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254927, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254927, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
  have h4 (q : Pattern) (selected : d254928 q = 0) : d256569 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254928, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254928, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254929 q = 0) : d256570 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254929, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254929, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254459 q = 0) : d256043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254459, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254459, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254460 q = 0) : d256044 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254460, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254460, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254462 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
    | true =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254463 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254464 q = 0) : d256048 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254464, d256048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254464, d256048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254938 q = 0) : d256578 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254938, d256578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254938, d256578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254939 q = 0) : d256579 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254939, d256579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254939, d256579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254941 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254941, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254941, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26048 q selected
  have h14 (q : Pattern) (selected : d254942 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254942, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254942, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25816 q selected
  have h15 (q : Pattern) (selected : d254943 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254943, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254943, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254944 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254944, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254944, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h17 (q : Pattern) (selected : d254945 q = 0) : d256585 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254945, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254945, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254946 q = 0) : d256586 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254946, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d254946, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d254947 q = 0) : d256587 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254947, d256587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254947, d256587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26050 (p : Pattern) (selected : d254956 p = 0) : d256596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254454 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254454, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25966 q selected
    | true =>
      simp only [d254454, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254455 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254455, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254455, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254459 q = 0) : d256043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254459, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254459, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254460 q = 0) : d256044 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254460, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254460, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254953 q = 0) : d256593 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254953, d256593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254953, d256593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254954 q = 0) : d256594 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254954, d256594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254954, d256594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254955 q = 0) : d256595 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254955, d256595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254955, d256595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254941 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254941, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254941, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26048 q selected
  have h9 (q : Pattern) (selected : d254942 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254942, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254942, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25816 q selected
  have h10 (q : Pattern) (selected : d254943 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254943, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254943, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254462 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
    | true =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254463 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254944 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254944, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254944, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254945 q = 0) : d256585 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254945, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254945, d256585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254946 q = 0) : d256586 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254946, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254946, d256586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254956 q = 0) : d256596 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254956, d256596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254956, d256596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro26051 (p : Pattern) (selected : d254964 p = 0) : d256604 p = 1 := by
  have h0 (q : Pattern) (selected : d254941 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254941, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254941, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26048 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d254942 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254942, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254942, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25816 q selected
  have h3 (q : Pattern) (selected : d254943 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254943, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254943, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254462 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
    | true =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d254463 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d254944 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254944, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254944, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254961 q = 0) : d256601 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254961, d256601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254961, d256601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d254962 q = 0) : d256602 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254962, d256602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254962, d256602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254963 q = 0) : d256603 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254963, d256603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254963, d256603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d254964 q = 0) : d256604 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254964, d256604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254964, d256604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h10 p selected
theorem eqIntro26052 (p : Pattern) (selected : d254970 p = 0) : d256610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254934 q = 0) : d256574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254934, d256574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26047 q selected
    | true =>
      simp only [d254934, d256574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254935 q = 0) : d256575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254935, d256575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254935, d256575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254936 q = 0) : d256576 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254936, d256576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254936, d256576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254937 q = 0) : d256577 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254937, d256577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254937, d256577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254948 q = 0) : d256588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254948, d256588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26049 q selected
    | true =>
      simp only [d254948, d256588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254949 q = 0) : d256589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254949, d256589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254949, d256589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254950 q = 0) : d256590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254950, d256590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254950, d256590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254951 q = 0) : d256591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254951, d256591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254951, d256591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254952 q = 0) : d256592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254952, d256592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254952, d256592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254957 q = 0) : d256597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254957, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26050 q selected
    | true =>
      simp only [d254957, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254958 q = 0) : d256598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254958, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254958, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254959 q = 0) : d256599 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254959, d256599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254959, d256599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254960 q = 0) : d256600 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254960, d256600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254960, d256600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d254965 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
    | true =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254966 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254967 q = 0) : d256607 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254967, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254967, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254968 q = 0) : d256608 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254968, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254968, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254969 q = 0) : d256609 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254969, d256609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254969, d256609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254970 q = 0) : d256610 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254970, d256610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254970, d256610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26053 (p : Pattern) (selected : d254971 p = 0) : d256611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254454 q = 0) : d256038 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254454, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25966 q selected
    | true =>
      simp only [d254454, d256038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254455 q = 0) : d256039 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254455, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254455, d256039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254927 q = 0) : d256568 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254927, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254927, d256568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
  have h4 (q : Pattern) (selected : d254928 q = 0) : d256569 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254928, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254928, d256569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254929 q = 0) : d256570 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254929, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254929, d256570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254459 q = 0) : d256043 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254459, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254459, d256043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254460 q = 0) : d256044 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254460, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254460, d256044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254462 q = 0) : d256046 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
    | true =>
      simp only [d254462, d256046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254463 q = 0) : d256047 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254463, d256047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254464 q = 0) : d256048 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254464, d256048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254464, d256048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254938 q = 0) : d256578 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254938, d256578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254938, d256578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254939 q = 0) : d256579 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254939, d256579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254939, d256579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254941 q = 0) : d256581 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254941, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25967 q selected
    | true =>
      simp only [d254941, d256581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26048 q selected
  have h14 (q : Pattern) (selected : d254942 q = 0) : d256582 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254942, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254942, d256582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25816 q selected
  have h15 (q : Pattern) (selected : d254943 q = 0) : d256583 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254943, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254943, d256583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254944 q = 0) : d256584 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254944, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254944, d256584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h17 (q : Pattern) (selected : d254961 q = 0) : d256601 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254961, d256601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254961, d256601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254962 q = 0) : d256602 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254962, d256602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254962, d256602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254963 q = 0) : d256603 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254963, d256603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d254963, d256603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d254971 q = 0) : d256611 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254971, d256611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254971, d256611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro26054 (p : Pattern) (selected : d254978 p = 0) : d256618 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254972 q = 0) : d256612 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254972, d256612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26053 q selected
    | true =>
      simp only [d254972, d256612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254973 q = 0) : d256613 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254973, d256613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254973, d256613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254974 q = 0) : d256614 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254974, d256614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254974, d256614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254975 q = 0) : d256615 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254975, d256615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254975, d256615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254965 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
    | true =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254966 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254967 q = 0) : d256607 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254967, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254967, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254968 q = 0) : d256608 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254968, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254968, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254976 q = 0) : d256616 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254976, d256616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254976, d256616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254977 q = 0) : d256617 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254977, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254977, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254978 q = 0) : d256618 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254978, d256618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254978, d256618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26055 (p : Pattern) (selected : d254982 p = 0) : d256622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254965 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
    | true =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254966 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254967 q = 0) : d256607 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254967, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254967, d256607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254968 q = 0) : d256608 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254968, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254968, d256608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254977 q = 0) : d256617 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254977, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254977, d256617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254982 q = 0) : d256622 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254982, d256622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254982, d256622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26056 (p : Pattern) (selected : d254989 p = 0) : d256629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254979 q = 0) : d256619 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254979, d256619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26052 q selected
    | true =>
      simp only [d254979, d256619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26054 q selected
  have h2 (q : Pattern) (selected : d254980 q = 0) : d256620 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254980, d256620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254980, d256620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254981 q = 0) : d256621 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254981, d256621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254981, d256621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254983 q = 0) : d256623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254983, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26054 q selected
    | true =>
      simp only [d254983, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26055 q selected
  have h5 (q : Pattern) (selected : d254984 q = 0) : d256624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254984, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254984, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254985 q = 0) : d256625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254985, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254985, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254986 q = 0) : d256626 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254986, d256626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254986, d256626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254987 q = 0) : d256627 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254987, d256627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254987, d256627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254988 q = 0) : d256628 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254988, d256628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254988, d256628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254989 q = 0) : d256629 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254989, d256629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254989, d256629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26057 (p : Pattern) (selected : d254993 p = 0) : d256633 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254983 q = 0) : d256623 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254983, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26054 q selected
    | true =>
      simp only [d254983, d256623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26055 q selected
  have h2 (q : Pattern) (selected : d254984 q = 0) : d256624 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254984, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254984, d256624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254985 q = 0) : d256625 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254985, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254985, d256625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254987 q = 0) : d256627 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254987, d256627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254987, d256627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254992 q = 0) : d256632 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254992, d256632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254992, d256632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254993 q = 0) : d256633 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254993, d256633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254993, d256633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26058 (p : Pattern) (selected : d254999 p = 0) : d256639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254990 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254990, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26056 q selected
    | true =>
      simp only [d254990, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254991 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254991, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254991, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254994 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254994, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26057 q selected
    | true =>
      simp only [d254994, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254995 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254995, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254995, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254996 q = 0) : d256636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254996, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254996, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254997 q = 0) : d256637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254997, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254997, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254998 q = 0) : d256638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254998, d256638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254998, d256638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254999 q = 0) : d256639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254999, d256639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254999, d256639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26059 (p : Pattern) (selected : d255003 p = 0) : d256643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254994 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254994, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26057 q selected
    | true =>
      simp only [d254994, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254995 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254995, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254995, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255000 q = 0) : d256640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255000, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255000, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255001 q = 0) : d256641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255001, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255001, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255002 q = 0) : d256642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255002, d256642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255002, d256642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255003 q = 0) : d256643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255003, d256643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255003, d256643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26060 (p : Pattern) (selected : d255009 p = 0) : d256722 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255006 q = 0) : d256719 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255006, d256719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255006, d256719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255007 q = 0) : d256720 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255007, d256720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255007, d256720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255008 q = 0) : d256721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255008, d256721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255008, d256721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255009 q = 0) : d256722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255009, d256722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255009, d256722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26061 (p : Pattern) (selected : d255015 p = 0) : d256728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254873 q = 0) : d256667 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254873, d256667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26036 q selected
    | true =>
      simp only [d254873, d256667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26037 q selected
  have h2 (q : Pattern) (selected : d254874 q = 0) : d256668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254874, d256668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254874, d256668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254875 q = 0) : d256669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254875, d256669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254875, d256669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254876 q = 0) : d256670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254876, d256670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254876, d256670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254883 q = 0) : d256677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254883, d256677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26038 q selected
    | true =>
      simp only [d254883, d256677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26039 q selected
  have h6 (q : Pattern) (selected : d254884 q = 0) : d256678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254884, d256678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254884, d256678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254885 q = 0) : d256679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254885, d256679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254885, d256679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254923 q = 0) : d256717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254923, d256717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26046 q selected
    | true =>
      simp only [d254923, d256717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26030 q selected
  have h9 (q : Pattern) (selected : d255004 q = 0) : d256644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255004, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26058 q selected
    | true =>
      simp only [d255004, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26059 q selected
  have h10 (q : Pattern) (selected : d255005 q = 0) : d256718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255005, d256718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255005, d256718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255010 q = 0) : d256723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255010, d256723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26060 q selected
    | true =>
      simp only [d255010, d256723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d255011 q = 0) : d256724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255011, d256724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255011, d256724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255012 q = 0) : d256725 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255012, d256725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255012, d256725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255013 q = 0) : d256726 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255013, d256726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255013, d256726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d255014 q = 0) : d256727 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255014, d256727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255014, d256727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d255015 q = 0) : d256728 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255015, d256728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255015, d256728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro26062 (p : Pattern) (selected : d255016 p = 0) : d256729 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254842 q = 0) : d256636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254843 q = 0) : d256637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254843, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254843, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254869 q = 0) : d256663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254869, d256663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254869, d256663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255016 q = 0) : d256729 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255016, d256729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255016, d256729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26063 (p : Pattern) (selected : d255017 p = 0) : d256730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254846 q = 0) : d256640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254847 q = 0) : d256641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254847, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254847, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254871 q = 0) : d256665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254871, d256665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254871, d256665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255017 q = 0) : d256730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255017, d256730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255017, d256730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26064 (p : Pattern) (selected : d255022 p = 0) : d256735 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254842 q = 0) : d256636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254842, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254877 q = 0) : d256671 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254877, d256671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254877, d256671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254878 q = 0) : d256672 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254878, d256672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254878, d256672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255022 q = 0) : d256735 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255022, d256735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255022, d256735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26065 (p : Pattern) (selected : d255023 p = 0) : d256736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254840 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26029 q selected
    | true =>
      simp only [d254840, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254841 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254841, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254846 q = 0) : d256640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254846, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254880 q = 0) : d256674 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254880, d256674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254880, d256674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254881 q = 0) : d256675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254881, d256675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254881, d256675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255023 q = 0) : d256736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255023, d256736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255023, d256736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26066 (p : Pattern) (selected : d255027 p = 0) : d256740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254917 q = 0) : d256711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254917, d256711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26045 q selected
    | true =>
      simp only [d254917, d256711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254918 q = 0) : d256712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254918, d256712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254918, d256712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254919 q = 0) : d256713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254919, d256713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254919, d256713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254920 q = 0) : d256714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254920, d256714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254920, d256714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254921 q = 0) : d256715 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254921, d256715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254921, d256715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255027 q = 0) : d256740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255027, d256740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255027, d256740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26067 (p : Pattern) (selected : d255029 p = 0) : d256652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254990 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254990, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26056 q selected
    | true =>
      simp only [d254990, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254991 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254991, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254991, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254994 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254994, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26057 q selected
    | true =>
      simp only [d254994, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254995 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254995, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254995, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254996 q = 0) : d256636 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254996, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254996, d256636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254997 q = 0) : d256637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254997, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254997, d256637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254998 q = 0) : d256638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254998, d256638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254998, d256638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255029 q = 0) : d256652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255029, d256652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255029, d256652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26068 (p : Pattern) (selected : d255030 p = 0) : d256653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254994 q = 0) : d256634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254994, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26057 q selected
    | true =>
      simp only [d254994, d256634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254995 q = 0) : d256635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254995, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254995, d256635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255000 q = 0) : d256640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255000, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255000, d256640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255001 q = 0) : d256641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255001, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255001, d256641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255002 q = 0) : d256642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255002, d256642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255002, d256642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255030 q = 0) : d256653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255030, d256653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255030, d256653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26069 (p : Pattern) (selected : d255033 p = 0) : d256743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254836 q = 0) : d256630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26028 q selected
    | true =>
      simp only [d254836, d256630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254837 q = 0) : d256631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254837, d256631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255006 q = 0) : d256719 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255006, d256719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255006, d256719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255007 q = 0) : d256720 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255007, d256720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255007, d256720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255008 q = 0) : d256721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255008, d256721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255008, d256721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255033 q = 0) : d256743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255033, d256743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255033, d256743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26070 (p : Pattern) (selected : d255039 p = 0) : d256749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254873 q = 0) : d256667 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254873, d256667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26036 q selected
    | true =>
      simp only [d254873, d256667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26037 q selected
  have h2 (q : Pattern) (selected : d254874 q = 0) : d256668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254874, d256668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254874, d256668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254875 q = 0) : d256669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254875, d256669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254875, d256669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254876 q = 0) : d256670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254876, d256670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254876, d256670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254883 q = 0) : d256677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254883, d256677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26038 q selected
    | true =>
      simp only [d254883, d256677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26039 q selected
  have h6 (q : Pattern) (selected : d254884 q = 0) : d256678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254884, d256678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254884, d256678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254885 q = 0) : d256679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254885, d256679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254885, d256679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254923 q = 0) : d256717 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254923, d256717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26046 q selected
    | true =>
      simp only [d254923, d256717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26030 q selected
  have h9 (q : Pattern) (selected : d255004 q = 0) : d256644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255004, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26058 q selected
    | true =>
      simp only [d255004, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26059 q selected
  have h10 (q : Pattern) (selected : d255005 q = 0) : d256718 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255005, d256718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255005, d256718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255010 q = 0) : d256723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255010, d256723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26060 q selected
    | true =>
      simp only [d255010, d256723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d255011 q = 0) : d256724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255011, d256724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255011, d256724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255012 q = 0) : d256725 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255012, d256725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255012, d256725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255013 q = 0) : d256726 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255013, d256726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255013, d256726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d255014 q = 0) : d256727 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255014, d256727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255014, d256727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d255018 q = 0) : d256731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255018, d256731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26062 q selected
    | true =>
      simp only [d255018, d256731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26063 q selected
  have h17 (q : Pattern) (selected : d255019 q = 0) : d256732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255019, d256732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255019, d256732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d255020 q = 0) : d256733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255020, d256733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d255020, d256733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d255021 q = 0) : d256734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255021, d256734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255021, d256734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d255024 q = 0) : d256737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255024, d256737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26064 q selected
    | true =>
      simp only [d255024, d256737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26065 q selected
  have h21 (q : Pattern) (selected : d255025 q = 0) : d256738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255025, d256738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255025, d256738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d255026 q = 0) : d256739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255026, d256739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d255026, d256739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d255028 q = 0) : d256741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255028, d256741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26066 q selected
    | true =>
      simp only [d255028, d256741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26033 q selected
  have h24 (q : Pattern) (selected : d255031 q = 0) : d256654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255031, d256654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26067 q selected
    | true =>
      simp only [d255031, d256654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26068 q selected
  have h25 (q : Pattern) (selected : d255032 q = 0) : d256742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255032, d256742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d255032, d256742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d255034 q = 0) : d256744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255034, d256744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26069 q selected
    | true =>
      simp only [d255034, d256744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d255035 q = 0) : d256745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255035, d256745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d255035, d256745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d255036 q = 0) : d256746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255036, d256746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d255036, d256746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d255037 q = 0) : d256747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255037, d256747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d255037, d256747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d255038 q = 0) : d256748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255038, d256748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d255038, d256748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d255039 q = 0) : d256749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255039, d256749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d255039, d256749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro26071 (p : Pattern) (selected : d255046 p = 0) : d256756 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254850 q = 0) : d256644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254850, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26030 q selected
    | true =>
      simp only [d254850, d256644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26031 q selected
  have h2 (q : Pattern) (selected : d254851 q = 0) : d256645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254851, d256645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254851, d256645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254852 q = 0) : d256646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254852, d256646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254852, d256646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254853 q = 0) : d256647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254853, d256647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254853, d256647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254854 q = 0) : d256648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254854, d256648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254854, d256648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255041 q = 0) : d256751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255041, d256751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26031 q selected
    | true =>
      simp only [d255041, d256751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255042 q = 0) : d256752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255042, d256752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255042, d256752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255043 q = 0) : d256753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255043, d256753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255043, d256753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255044 q = 0) : d256754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255044, d256754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255044, d256754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255045 q = 0) : d256755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255045, d256755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255045, d256755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255046 q = 0) : d256756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255046, d256756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255046, d256756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26072 (p : Pattern) (selected : d255052 p = 0) : d256762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255041 q = 0) : d256751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255041, d256751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26031 q selected
    | true =>
      simp only [d255041, d256751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255042 q = 0) : d256752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255042, d256752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255042, d256752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255043 q = 0) : d256753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255043, d256753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255043, d256753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255044 q = 0) : d256754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255044, d256754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255044, d256754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255045 q = 0) : d256755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255045, d256755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255045, d256755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255047 q = 0) : d256757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255047, d256757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26034 q selected
    | true =>
      simp only [d255047, d256757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255048 q = 0) : d256758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255048, d256758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255048, d256758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255049 q = 0) : d256759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255049, d256759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255049, d256759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255050 q = 0) : d256760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255050, d256760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255050, d256760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255051 q = 0) : d256761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255051, d256761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255051, d256761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255052 q = 0) : d256762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255052, d256762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255052, d256762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26073 (p : Pattern) (selected : d255059 p = 0) : d256769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255028 q = 0) : d256741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255028, d256741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26066 q selected
    | true =>
      simp only [d255028, d256741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26033 q selected
  have h2 (q : Pattern) (selected : d255031 q = 0) : d256654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255031, d256654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26067 q selected
    | true =>
      simp only [d255031, d256654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26068 q selected
  have h3 (q : Pattern) (selected : d255032 q = 0) : d256742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255032, d256742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255032, d256742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255034 q = 0) : d256744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255034, d256744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26069 q selected
    | true =>
      simp only [d255034, d256744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255035 q = 0) : d256745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255035, d256745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255035, d256745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255036 q = 0) : d256746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255036, d256746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255036, d256746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255057 q = 0) : d256767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255057, d256767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255057, d256767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255058 q = 0) : d256768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255058, d256768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255058, d256768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255059 q = 0) : d256769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255059, d256769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255059, d256769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro26074 (p : Pattern) (selected : d255061 p = 0) : d256771 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255047 q = 0) : d256757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255047, d256757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26034 q selected
    | true =>
      simp only [d255047, d256757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255048 q = 0) : d256758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255048, d256758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255048, d256758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255049 q = 0) : d256759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255049, d256759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255049, d256759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255050 q = 0) : d256760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255050, d256760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255050, d256760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255051 q = 0) : d256761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255051, d256761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255051, d256761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255061 q = 0) : d256771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255061, d256771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255061, d256771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26075 (p : Pattern) (selected : d255081 p = 0) : d256791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255067 q = 0) : d256777 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255067, d256777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255067, d256777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26040 q selected
  have h2 (q : Pattern) (selected : d254887 q = 0) : d256681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254887, d256681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26040 q selected
    | true =>
      simp only [d254887, d256681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255068 q = 0) : d256778 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255068, d256778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255068, d256778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254888 q = 0) : d256682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254888, d256682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254888, d256682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255069 q = 0) : d256779 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255069, d256779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255069, d256779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255070 q = 0) : d256780 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255070, d256780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255070, d256780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255071 q = 0) : d256781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255071, d256781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255071, d256781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26041 q selected
  have h8 (q : Pattern) (selected : d254892 q = 0) : d256686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254892, d256686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26041 q selected
    | true =>
      simp only [d254892, d256686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255072 q = 0) : d256782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255072, d256782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255072, d256782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254893 q = 0) : d256687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254893, d256687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254893, d256687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255073 q = 0) : d256783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255073, d256783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255073, d256783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255074 q = 0) : d256784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255074, d256784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255074, d256784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255075 q = 0) : d256785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255075, d256785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255075, d256785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255076 q = 0) : d256786 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255076, d256786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255076, d256786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26022 q selected
  have h15 (q : Pattern) (selected : d254803 q = 0) : d256597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254803, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26022 q selected
    | true =>
      simp only [d254803, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d255077 q = 0) : d256787 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255077, d256787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d255077, d256787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254804 q = 0) : d256598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254804, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254804, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d255078 q = 0) : d256788 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255078, d256788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d255078, d256788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d255079 q = 0) : d256789 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255079, d256789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d255079, d256789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d255080 q = 0) : d256790 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255080, d256790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255080, d256790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d255081 q = 0) : d256791 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255081, d256791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255081, d256791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro26076 (p : Pattern) (selected : d255096 p = 0) : d256806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255082 q = 0) : d256792 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255082, d256792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255082, d256792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26019 q selected
  have h2 (q : Pattern) (selected : d254780 q = 0) : d256574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254780, d256574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26019 q selected
    | true =>
      simp only [d254780, d256574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255083 q = 0) : d256793 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255083, d256793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255083, d256793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254781 q = 0) : d256575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254781, d256575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254781, d256575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255084 q = 0) : d256794 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255084, d256794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255084, d256794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255085 q = 0) : d256795 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255085, d256795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255085, d256795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255086 q = 0) : d256796 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255086, d256796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255086, d256796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26021 q selected
  have h8 (q : Pattern) (selected : d254794 q = 0) : d256588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254794, d256588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26021 q selected
    | true =>
      simp only [d254794, d256588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255087 q = 0) : d256797 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255087, d256797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255087, d256797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254795 q = 0) : d256589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254795, d256589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254795, d256589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255088 q = 0) : d256798 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255088, d256798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255088, d256798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255089 q = 0) : d256799 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255089, d256799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255089, d256799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255090 q = 0) : d256800 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255090, d256800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255090, d256800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255076 q = 0) : d256786 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255076, d256786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255076, d256786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26022 q selected
  have h15 (q : Pattern) (selected : d254803 q = 0) : d256597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254803, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26022 q selected
    | true =>
      simp only [d254803, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d255077 q = 0) : d256787 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255077, d256787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d255077, d256787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254804 q = 0) : d256598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254804, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254804, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d255078 q = 0) : d256788 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255078, d256788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d255078, d256788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d255079 q = 0) : d256789 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255079, d256789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d255079, d256789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d255091 q = 0) : d256801 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255091, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255091, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
  have h21 (q : Pattern) (selected : d254811 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
    | true =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d255092 q = 0) : d256802 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255092, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d255092, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d254812 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d255093 q = 0) : d256803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255093, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d255093, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d255094 q = 0) : d256804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255094, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d255094, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d255095 q = 0) : d256805 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255095, d256805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d255095, d256805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d255096 q = 0) : d256806 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255096, d256806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255096, d256806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro26077 (p : Pattern) (selected : d255106 p = 0) : d256816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255100 q = 0) : d256810 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255100, d256810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255100, d256810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26043 q selected
  have h2 (q : Pattern) (selected : d254905 q = 0) : d256699 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254905, d256699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26043 q selected
    | true =>
      simp only [d254905, d256699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255101 q = 0) : d256811 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255101, d256811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255101, d256811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254906 q = 0) : d256700 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254906, d256700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254906, d256700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255102 q = 0) : d256812 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255102, d256812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255102, d256812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255103 q = 0) : d256813 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255103, d256813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255103, d256813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255091 q = 0) : d256801 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255091, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255091, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
  have h8 (q : Pattern) (selected : d254811 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
    | true =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255092 q = 0) : d256802 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255092, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255092, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254812 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255093 q = 0) : d256803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255093, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255093, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255094 q = 0) : d256804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255094, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255094, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255104 q = 0) : d256814 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255104, d256814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255104, d256814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255105 q = 0) : d256815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255105, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255105, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d255106 q = 0) : d256816 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255106, d256816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255106, d256816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26078 (p : Pattern) (selected : d255116 p = 0) : d256826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255111 q = 0) : d256821 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255111, d256821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255111, d256821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26025 q selected
  have h2 (q : Pattern) (selected : d254818 q = 0) : d256612 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254818, d256612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26025 q selected
    | true =>
      simp only [d254818, d256612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255112 q = 0) : d256822 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255112, d256822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255112, d256822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254819 q = 0) : d256613 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254819, d256613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254819, d256613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255113 q = 0) : d256823 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255113, d256823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255113, d256823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255114 q = 0) : d256824 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255114, d256824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255114, d256824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255091 q = 0) : d256801 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255091, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255091, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
  have h8 (q : Pattern) (selected : d254811 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
    | true =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255092 q = 0) : d256802 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255092, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255092, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254812 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255093 q = 0) : d256803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255093, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255093, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255094 q = 0) : d256804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255094, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255094, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255115 q = 0) : d256825 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255115, d256825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255115, d256825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255105 q = 0) : d256815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255105, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255105, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d255116 q = 0) : d256826 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255116, d256826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255116, d256826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26079 (p : Pattern) (selected : d255120 p = 0) : d256830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255091 q = 0) : d256801 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255091, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255091, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
  have h2 (q : Pattern) (selected : d254811 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26023 q selected
    | true =>
      simp only [d254811, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255092 q = 0) : d256802 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255092, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255092, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254812 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254812, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255093 q = 0) : d256803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255093, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255093, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255094 q = 0) : d256804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255094, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255094, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255105 q = 0) : d256815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255105, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255105, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255120 q = 0) : d256830 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255120, d256830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255120, d256830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26080 (p : Pattern) (selected : d255126 p = 0) : d256836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255097 q = 0) : d256807 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255097, d256807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26075 q selected
    | true =>
      simp only [d255097, d256807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26076 q selected
  have h2 (q : Pattern) (selected : d255098 q = 0) : d256808 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255098, d256808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255098, d256808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255099 q = 0) : d256809 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255099, d256809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255099, d256809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255107 q = 0) : d256817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255107, d256817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26076 q selected
    | true =>
      simp only [d255107, d256817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26077 q selected
  have h5 (q : Pattern) (selected : d255108 q = 0) : d256818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255108, d256818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255108, d256818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255109 q = 0) : d256819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255109, d256819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255109, d256819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255110 q = 0) : d256820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255110, d256820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255110, d256820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255117 q = 0) : d256827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255117, d256827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26076 q selected
    | true =>
      simp only [d255117, d256827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26078 q selected
  have h9 (q : Pattern) (selected : d255118 q = 0) : d256828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255118, d256828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255118, d256828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255119 q = 0) : d256829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255119, d256829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255119, d256829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255121 q = 0) : d256831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255121, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26078 q selected
    | true =>
      simp only [d255121, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26079 q selected
  have h12 (q : Pattern) (selected : d255122 q = 0) : d256832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255122, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255122, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d255123 q = 0) : d256833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255123, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255123, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255124 q = 0) : d256834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255124, d256834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255124, d256834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d255125 q = 0) : d256835 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255125, d256835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255125, d256835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d255126 q = 0) : d256836 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255126, d256836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d255126, d256836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro26081 (p : Pattern) (selected : d255131 p = 0) : d256841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255117 q = 0) : d256827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255117, d256827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26076 q selected
    | true =>
      simp only [d255117, d256827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26078 q selected
  have h2 (q : Pattern) (selected : d255118 q = 0) : d256828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255118, d256828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255118, d256828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255119 q = 0) : d256829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255119, d256829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255119, d256829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255121 q = 0) : d256831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255121, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26078 q selected
    | true =>
      simp only [d255121, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26079 q selected
  have h5 (q : Pattern) (selected : d255122 q = 0) : d256832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255122, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255122, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255123 q = 0) : d256833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255123, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255123, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255124 q = 0) : d256834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255124, d256834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255124, d256834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255129 q = 0) : d256839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255129, d256839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255129, d256839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255130 q = 0) : d256840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255130, d256840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255130, d256840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255131 q = 0) : d256841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255131, d256841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255131, d256841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26082 (p : Pattern) (selected : d255137 p = 0) : d256847 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255127 q = 0) : d256837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255127, d256837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26080 q selected
    | true =>
      simp only [d255127, d256837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255128 q = 0) : d256838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255128, d256838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255128, d256838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255132 q = 0) : d256842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255132, d256842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26081 q selected
    | true =>
      simp only [d255132, d256842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255133 q = 0) : d256843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255133, d256843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255133, d256843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255134 q = 0) : d256844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255134, d256844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255134, d256844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255135 q = 0) : d256845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255135, d256845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255135, d256845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255136 q = 0) : d256846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255136, d256846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255136, d256846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255137 q = 0) : d256847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255137, d256847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255137, d256847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26083 (p : Pattern) (selected : d255139 p = 0) : d256849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255121 q = 0) : d256831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255121, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26078 q selected
    | true =>
      simp only [d255121, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26079 q selected
  have h2 (q : Pattern) (selected : d255122 q = 0) : d256832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255122, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255122, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255123 q = 0) : d256833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255123, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255123, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255129 q = 0) : d256839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255129, d256839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255129, d256839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255138 q = 0) : d256848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255138, d256848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255138, d256848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255139 q = 0) : d256849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255139, d256849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255139, d256849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26084 (p : Pattern) (selected : d255145 p = 0) : d256855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255132 q = 0) : d256842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255132, d256842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26081 q selected
    | true =>
      simp only [d255132, d256842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255133 q = 0) : d256843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255133, d256843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255133, d256843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255140 q = 0) : d256850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255140, d256850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26083 q selected
    | true =>
      simp only [d255140, d256850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255141 q = 0) : d256851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255141, d256851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255141, d256851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255142 q = 0) : d256852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255142, d256852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255142, d256852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255143 q = 0) : d256853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255143, d256853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255143, d256853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255144 q = 0) : d256854 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255144, d256854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255144, d256854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255145 q = 0) : d256855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255145, d256855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255145, d256855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26085 (p : Pattern) (selected : d255165 p = 0) : d256806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255147 q = 0) : d256792 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255147, d256792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255147, d256792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26047 q selected
  have h2 (q : Pattern) (selected : d254934 q = 0) : d256574 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254934, d256574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26047 q selected
    | true =>
      simp only [d254934, d256574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255148 q = 0) : d256793 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255148, d256793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255148, d256793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254935 q = 0) : d256575 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254935, d256575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254935, d256575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255149 q = 0) : d256794 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255149, d256794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255149, d256794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255150 q = 0) : d256795 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255150, d256795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255150, d256795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255151 q = 0) : d256796 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255151, d256796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255151, d256796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26049 q selected
  have h8 (q : Pattern) (selected : d254948 q = 0) : d256588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254948, d256588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26049 q selected
    | true =>
      simp only [d254948, d256588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255152 q = 0) : d256797 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255152, d256797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255152, d256797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254949 q = 0) : d256589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254949, d256589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254949, d256589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255153 q = 0) : d256798 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255153, d256798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255153, d256798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255154 q = 0) : d256799 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255154, d256799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255154, d256799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255155 q = 0) : d256800 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255155, d256800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255155, d256800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255156 q = 0) : d256786 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255156, d256786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255156, d256786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26050 q selected
  have h15 (q : Pattern) (selected : d254957 q = 0) : d256597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254957, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26050 q selected
    | true =>
      simp only [d254957, d256597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d255157 q = 0) : d256787 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255157, d256787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d255157, d256787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254958 q = 0) : d256598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254958, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254958, d256598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d255158 q = 0) : d256788 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255158, d256788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d255158, d256788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d255159 q = 0) : d256789 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255159, d256789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d255159, d256789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d255160 q = 0) : d256801 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255160, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255160, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
  have h21 (q : Pattern) (selected : d254965 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
    | true =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d255161 q = 0) : d256802 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255161, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d255161, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d254966 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d255162 q = 0) : d256803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255162, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d255162, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d255163 q = 0) : d256804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255163, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d255163, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d255164 q = 0) : d256805 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255164, d256805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d255164, d256805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d255165 q = 0) : d256806 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255165, d256806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255165, d256806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro26086 (p : Pattern) (selected : d255172 p = 0) : d256826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255166 q = 0) : d256821 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255166, d256821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255166, d256821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26053 q selected
  have h2 (q : Pattern) (selected : d254972 q = 0) : d256612 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254972, d256612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26053 q selected
    | true =>
      simp only [d254972, d256612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255167 q = 0) : d256822 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255167, d256822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255167, d256822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254973 q = 0) : d256613 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254973, d256613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254973, d256613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255168 q = 0) : d256823 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255168, d256823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255168, d256823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255169 q = 0) : d256824 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255169, d256824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255169, d256824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255160 q = 0) : d256801 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255160, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255160, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
  have h8 (q : Pattern) (selected : d254965 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
    | true =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255161 q = 0) : d256802 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255161, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255161, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254966 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255162 q = 0) : d256803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255162, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255162, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255163 q = 0) : d256804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255163, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255163, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255170 q = 0) : d256825 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255170, d256825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255170, d256825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255171 q = 0) : d256815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255171, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255171, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d255172 q = 0) : d256826 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255172, d256826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255172, d256826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26087 (p : Pattern) (selected : d255176 p = 0) : d256830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255160 q = 0) : d256801 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255160, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255160, d256801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
  have h2 (q : Pattern) (selected : d254965 q = 0) : d256605 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26051 q selected
    | true =>
      simp only [d254965, d256605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255161 q = 0) : d256802 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255161, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255161, d256802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254966 q = 0) : d256606 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254966, d256606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255162 q = 0) : d256803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255162, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255162, d256803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255163 q = 0) : d256804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255163, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255163, d256804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255171 q = 0) : d256815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255171, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255171, d256815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255176 q = 0) : d256830 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255176, d256830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255176, d256830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26088 (p : Pattern) (selected : d255183 p = 0) : d256841 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255173 q = 0) : d256827 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255173, d256827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26085 q selected
    | true =>
      simp only [d255173, d256827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26086 q selected
  have h2 (q : Pattern) (selected : d255174 q = 0) : d256828 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255174, d256828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255174, d256828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255175 q = 0) : d256829 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255175, d256829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255175, d256829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255177 q = 0) : d256831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255177, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26086 q selected
    | true =>
      simp only [d255177, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26087 q selected
  have h5 (q : Pattern) (selected : d255178 q = 0) : d256832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255178, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255178, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255179 q = 0) : d256833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255179, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255179, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255180 q = 0) : d256834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255180, d256834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255180, d256834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255181 q = 0) : d256839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255181, d256839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255181, d256839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255182 q = 0) : d256840 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255182, d256840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255182, d256840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255183 q = 0) : d256841 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255183, d256841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255183, d256841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26089 (p : Pattern) (selected : d255187 p = 0) : d256849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255177 q = 0) : d256831 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255177, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26086 q selected
    | true =>
      simp only [d255177, d256831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26087 q selected
  have h2 (q : Pattern) (selected : d255178 q = 0) : d256832 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255178, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255178, d256832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255179 q = 0) : d256833 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255179, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255179, d256833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255181 q = 0) : d256839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255181, d256839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255181, d256839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255186 q = 0) : d256848 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255186, d256848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255186, d256848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255187 q = 0) : d256849 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255187, d256849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255187, d256849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26090 (p : Pattern) (selected : d255193 p = 0) : d256855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255184 q = 0) : d256842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255184, d256842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26088 q selected
    | true =>
      simp only [d255184, d256842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255185 q = 0) : d256843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255185, d256843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255185, d256843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255188 q = 0) : d256850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255188, d256850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26089 q selected
    | true =>
      simp only [d255188, d256850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255189 q = 0) : d256851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255189, d256851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255189, d256851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255190 q = 0) : d256852 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255190, d256852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255190, d256852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255191 q = 0) : d256853 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255191, d256853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255191, d256853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255192 q = 0) : d256854 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255192, d256854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255192, d256854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255193 q = 0) : d256855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255193, d256855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255193, d256855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26091 (p : Pattern) (selected : d255197 p = 0) : d256860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255188 q = 0) : d256850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255188, d256850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26089 q selected
    | true =>
      simp only [d255188, d256850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255189 q = 0) : d256851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255189, d256851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255189, d256851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255194 q = 0) : d256857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255194, d256857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255194, d256857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255195 q = 0) : d256858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255195, d256858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255195, d256858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255196 q = 0) : d256859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255196, d256859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255196, d256859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255197 q = 0) : d256860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255197, d256860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255197, d256860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26092 (p : Pattern) (selected : d255203 p = 0) : d256866 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255132 q = 0) : d256842 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255132, d256842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26081 q selected
    | true =>
      simp only [d255132, d256842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255133 q = 0) : d256843 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255133, d256843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255133, d256843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255200 q = 0) : d256863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255200, d256863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255200, d256863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255201 q = 0) : d256864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255201, d256864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255201, d256864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255202 q = 0) : d256865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255202, d256865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255202, d256865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255203 q = 0) : d256866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255203, d256866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255203, d256866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26093 (p : Pattern) (selected : d255209 p = 0) : d256872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255146 q = 0) : d256856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255146, d256856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26082 q selected
    | true =>
      simp only [d255146, d256856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26084 q selected
  have h2 (q : Pattern) (selected : d255198 q = 0) : d256861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255198, d256861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26090 q selected
    | true =>
      simp only [d255198, d256861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26091 q selected
  have h3 (q : Pattern) (selected : d255199 q = 0) : d256862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255199, d256862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255199, d256862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255204 q = 0) : d256867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255204, d256867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26092 q selected
    | true =>
      simp only [d255204, d256867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255205 q = 0) : d256868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255205, d256868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255205, d256868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255206 q = 0) : d256869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255206, d256869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255206, d256869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255207 q = 0) : d256870 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255207, d256870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255207, d256870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255208 q = 0) : d256871 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255208, d256871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255208, d256871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255209 q = 0) : d256872 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255209, d256872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255209, d256872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro26094 (p : Pattern) (selected : d255214 p = 0) : d256860 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255140 q = 0) : d256850 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255140, d256850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26083 q selected
    | true =>
      simp only [d255140, d256850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255141 q = 0) : d256851 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255141, d256851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255141, d256851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255211 q = 0) : d256857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255211, d256857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255211, d256857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255212 q = 0) : d256858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255212, d256858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255212, d256858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255213 q = 0) : d256859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255213, d256859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255213, d256859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255214 q = 0) : d256860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255214, d256860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255214, d256860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26095 (p : Pattern) (selected : d255220 p = 0) : d256879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255215 q = 0) : d256874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255215, d256874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26094 q selected
    | true =>
      simp only [d255215, d256874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255216 q = 0) : d256875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255216, d256875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255216, d256875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255217 q = 0) : d256876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255217, d256876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255217, d256876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255218 q = 0) : d256877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255218, d256877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255218, d256877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255219 q = 0) : d256878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255219, d256878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255219, d256878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255220 q = 0) : d256879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255220, d256879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255220, d256879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26096 (p : Pattern) (selected : d255226 p = 0) : d256885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d254856 q = 0) : d256650 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254856, d256650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254856, d256650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26032 q selected
  have h2 (q : Pattern) (selected : d254857 q = 0) : d256651 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254857, d256651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254857, d256651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254866 q = 0) : d256660 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254866, d256660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26032 q selected
    | true =>
      simp only [d254866, d256660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26035 q selected
  have h4 (q : Pattern) (selected : d254867 q = 0) : d256661 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254867, d256661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254867, d256661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254868 q = 0) : d256662 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d254868, d256662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254868, d256662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255040 q = 0) : d256750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255040, d256750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26061 q selected
    | true =>
      simp only [d255040, d256750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26070 q selected
  have h7 (q : Pattern) (selected : d255053 q = 0) : d256763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255053, d256763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26071 q selected
    | true =>
      simp only [d255053, d256763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26072 q selected
  have h8 (q : Pattern) (selected : d255054 q = 0) : d256764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255054, d256764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255054, d256764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255055 q = 0) : d256765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255055, d256765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255055, d256765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d255056 q = 0) : d256766 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255056, d256766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255056, d256766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255060 q = 0) : d256770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255060, d256770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255060, d256770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26073 q selected
  have h12 (q : Pattern) (selected : d255062 q = 0) : d256772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255062, d256772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255062, d256772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26074 q selected
  have h13 (q : Pattern) (selected : d255063 q = 0) : d256773 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255063, d256773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255063, d256773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255064 q = 0) : d256774 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255064, d256774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255064, d256774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d255065 q = 0) : d256775 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255065, d256775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d255065, d256775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d255066 q = 0) : d256776 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d255066, d256776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255066, d256776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d255210 q = 0) : d256873 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255210, d256873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255210, d256873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26093 q selected
  have h18 (q : Pattern) (selected : d255221 q = 0) : d256880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255221, d256880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255221, d256880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26095 q selected
  have h19 (q : Pattern) (selected : d255222 q = 0) : d256881 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255222, d256881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d255222, d256881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d255223 q = 0) : d256882 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255223, d256882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d255223, d256882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d255224 q = 0) : d256883 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255224, d256883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d255224, d256883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d255225 q = 0) : d256884 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d255225, d256884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d255225, d256884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d255226 q = 0) : d256885 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d255226, d256885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d255226, d256885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro26097 (p : Pattern) (selected : d255232 p = 0) : d256891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255227 q = 0) : d256886 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d255227, d256886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255227, d256886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26096 q selected
  have h2 (q : Pattern) (selected : d255228 q = 0) : d256887 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d255228, d256887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255228, d256887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255229 q = 0) : d256888 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d255229, d256888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255229, d256888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255230 q = 0) : d256889 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d255230, d256889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255230, d256889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255231 q = 0) : d256890 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d255231, d256890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255231, d256890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255232 q = 0) : d256891 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d255232, d256891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255232, d256891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26098 (p : Pattern) (selected : d255237 p = 0) : d256896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d308 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253788 q = 0) : d255849 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d253788, d255849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253788, d255849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255237 q = 0) : d256896 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d255237, d256896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255237, d256896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro26099 (p : Pattern) (selected : d255244 p = 0) : d256903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255238 q = 0) : d256897 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d255238, d256897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255238, d256897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26098 q selected
  have h2 (q : Pattern) (selected : d255239 q = 0) : d256898 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d255239, d256898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255239, d256898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
  have h3 (q : Pattern) (selected : d255240 q = 0) : d256899 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d255240, d256899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255240, d256899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255241 q = 0) : d256900 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d255241, d256900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255241, d256900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255242 q = 0) : d256901 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d255242, d256901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255242, d256901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255243 q = 0) : d256902 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d255243, d256902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255243, d256902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255244 q = 0) : d256903 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d255244, d256903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255244, d256903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro26100 (p : Pattern) (selected : d255250 p = 0) : d256909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255238 q = 0) : d256897 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d255238, d256897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255238, d256897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26098 q selected
  have h2 (q : Pattern) (selected : d255239 q = 0) : d256898 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d255239, d256898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255239, d256898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25889 q selected
  have h3 (q : Pattern) (selected : d255240 q = 0) : d256899 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d255240, d256899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255240, d256899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255241 q = 0) : d256900 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d255241, d256900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255241, d256900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255242 q = 0) : d256901 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d255242, d256901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255242, d256901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255243 q = 0) : d256902 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d255243, d256902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255243, d256902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255250 q = 0) : d256909 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d255250, d256909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255250, d256909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro26101 (p : Pattern) (selected : d255256 p = 0) : d256915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255245 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
    | true =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255246 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255247 q = 0) : d256906 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255247, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255247, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255248 q = 0) : d256907 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255248, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255248, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255249 q = 0) : d256908 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255249, d256908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255249, d256908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255251 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
    | true =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255252 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255253 q = 0) : d256912 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255253, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255253, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255254 q = 0) : d256913 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255254, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255254, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d255255 q = 0) : d256914 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255255, d256914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255255, d256914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255256 q = 0) : d256915 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255256, d256915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255256, d256915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26102 (p : Pattern) (selected : d255258 p = 0) : d256917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255245 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
    | true =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255246 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255247 q = 0) : d256906 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255247, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255247, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255248 q = 0) : d256907 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255248, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255248, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255251 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
    | true =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255252 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255253 q = 0) : d256912 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255253, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255253, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255254 q = 0) : d256913 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255254, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255254, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255255 q = 0) : d256914 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255255, d256914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255255, d256914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255257 q = 0) : d256916 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255257, d256916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255257, d256916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255258 q = 0) : d256917 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255258, d256917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255258, d256917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26103 (p : Pattern) (selected : d255262 p = 0) : d256921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255251 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
    | true =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255252 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255253 q = 0) : d256912 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255253, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255253, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255254 q = 0) : d256913 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255254, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255254, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255257 q = 0) : d256916 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255257, d256916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255257, d256916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255262 q = 0) : d256921 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255262, d256921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255262, d256921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26104 (p : Pattern) (selected : d255269 p = 0) : d256928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255259 q = 0) : d256918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255259, d256918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26101 q selected
    | true =>
      simp only [d255259, d256918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26102 q selected
  have h2 (q : Pattern) (selected : d255260 q = 0) : d256919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255260, d256919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255260, d256919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255261 q = 0) : d256920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255261, d256920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255261, d256920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255263 q = 0) : d256922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255263, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26102 q selected
    | true =>
      simp only [d255263, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26103 q selected
  have h5 (q : Pattern) (selected : d255264 q = 0) : d256923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255264, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255264, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255265 q = 0) : d256924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255265, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255265, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255266 q = 0) : d256925 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255266, d256925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255266, d256925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255267 q = 0) : d256926 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255267, d256926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255267, d256926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255268 q = 0) : d256927 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255268, d256927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255268, d256927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255269 q = 0) : d256928 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255269, d256928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255269, d256928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26105 (p : Pattern) (selected : d255273 p = 0) : d256932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255263 q = 0) : d256922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255263, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26102 q selected
    | true =>
      simp only [d255263, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26103 q selected
  have h2 (q : Pattern) (selected : d255264 q = 0) : d256923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255264, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255264, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255265 q = 0) : d256924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255265, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255265, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255267 q = 0) : d256926 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255267, d256926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255267, d256926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255272 q = 0) : d256931 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255272, d256931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255272, d256931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255273 q = 0) : d256932 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255273, d256932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255273, d256932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26106 (p : Pattern) (selected : d255279 p = 0) : d256938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255276 q = 0) : d256935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255277 q = 0) : d256936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255277, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255277, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255278 q = 0) : d256937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255278, d256937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255278, d256937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255279 q = 0) : d256938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255279, d256938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255279, d256938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26107 (p : Pattern) (selected : d255283 p = 0) : d256942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255280 q = 0) : d256939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255281 q = 0) : d256940 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255281, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255281, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255282 q = 0) : d256941 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255282, d256941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255282, d256941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255283 q = 0) : d256942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255283, d256942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255283, d256942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26108 (p : Pattern) (selected : d255289 p = 0) : d256948 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255284 q = 0) : d256943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255284, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26106 q selected
    | true =>
      simp only [d255284, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26107 q selected
  have h2 (q : Pattern) (selected : d255285 q = 0) : d256944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255285, d256944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255285, d256944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255286 q = 0) : d256945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255286, d256945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255286, d256945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255287 q = 0) : d256946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255287, d256946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255287, d256946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255288 q = 0) : d256947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255288, d256947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255288, d256947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255289 q = 0) : d256948 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255289, d256948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255289, d256948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26109 (p : Pattern) (selected : d255292 p = 0) : d256951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255276 q = 0) : d256935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255277 q = 0) : d256936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255277, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255277, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255278 q = 0) : d256937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255278, d256937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255278, d256937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255292 q = 0) : d256951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255292, d256951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255292, d256951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26110 (p : Pattern) (selected : d255293 p = 0) : d256952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255280 q = 0) : d256939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255281 q = 0) : d256940 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255281, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255281, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255282 q = 0) : d256941 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255282, d256941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255282, d256941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255293 q = 0) : d256952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255293, d256952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255293, d256952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26111 (p : Pattern) (selected : d255299 p = 0) : d256958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255284 q = 0) : d256943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255284, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26106 q selected
    | true =>
      simp only [d255284, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26107 q selected
  have h2 (q : Pattern) (selected : d255285 q = 0) : d256944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255285, d256944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255285, d256944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255286 q = 0) : d256945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255286, d256945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255286, d256945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255287 q = 0) : d256946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255287, d256946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255287, d256946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255288 q = 0) : d256947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255288, d256947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255288, d256947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255294 q = 0) : d256953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255294, d256953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26109 q selected
    | true =>
      simp only [d255294, d256953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26110 q selected
  have h7 (q : Pattern) (selected : d255295 q = 0) : d256954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255295, d256954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255295, d256954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255296 q = 0) : d256955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255296, d256955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255296, d256955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255297 q = 0) : d256956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255297, d256956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255297, d256956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255298 q = 0) : d256957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255298, d256957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255298, d256957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255299 q = 0) : d256958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255299, d256958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255299, d256958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26112 (p : Pattern) (selected : d255304 p = 0) : d256963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255276 q = 0) : d256935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255277 q = 0) : d256936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255277, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255277, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255303 q = 0) : d256962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255303, d256962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255303, d256962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255304 q = 0) : d256963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255304, d256963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255304, d256963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26113 (p : Pattern) (selected : d255306 p = 0) : d256965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255280 q = 0) : d256939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255281 q = 0) : d256940 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255281, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255281, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255305 q = 0) : d256964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255305, d256964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255305, d256964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255306 q = 0) : d256965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255306, d256965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255306, d256965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26114 (p : Pattern) (selected : d255313 p = 0) : d256972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255276 q = 0) : d256935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255311 q = 0) : d256970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255311, d256970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255311, d256970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255312 q = 0) : d256971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255312, d256971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255312, d256971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255313 q = 0) : d256972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255313, d256972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255313, d256972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26115 (p : Pattern) (selected : d255316 p = 0) : d256975 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255280 q = 0) : d256939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255314 q = 0) : d256973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255314, d256973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255314, d256973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255315 q = 0) : d256974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255315, d256974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255315, d256974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255316 q = 0) : d256975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255316, d256975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255316, d256975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26116 (p : Pattern) (selected : d255320 p = 0) : d256979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255245 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
    | true =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255246 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255247 q = 0) : d256906 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255247, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255247, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255248 q = 0) : d256907 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255248, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255248, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255249 q = 0) : d256908 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255249, d256908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255249, d256908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255320 q = 0) : d256979 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255320, d256979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255320, d256979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26117 (p : Pattern) (selected : d255326 p = 0) : d256985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255321 q = 0) : d256980 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255321, d256980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26116 q selected
    | true =>
      simp only [d255321, d256980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26101 q selected
  have h2 (q : Pattern) (selected : d255322 q = 0) : d256981 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255322, d256981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255322, d256981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255323 q = 0) : d256982 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255323, d256982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255323, d256982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255259 q = 0) : d256918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255259, d256918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26101 q selected
    | true =>
      simp only [d255259, d256918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26102 q selected
  have h5 (q : Pattern) (selected : d255260 q = 0) : d256919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255260, d256919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255260, d256919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255261 q = 0) : d256920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255261, d256920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255261, d256920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255324 q = 0) : d256983 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255324, d256983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255324, d256983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255263 q = 0) : d256922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255263, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26102 q selected
    | true =>
      simp only [d255263, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26103 q selected
  have h9 (q : Pattern) (selected : d255264 q = 0) : d256923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255264, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255264, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255265 q = 0) : d256924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255265, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255265, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255266 q = 0) : d256925 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255266, d256925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255266, d256925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255325 q = 0) : d256984 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255325, d256984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255325, d256984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d255326 q = 0) : d256985 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255326, d256985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255326, d256985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro26118 (p : Pattern) (selected : d255332 p = 0) : d256991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255327 q = 0) : d256986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255327, d256986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26117 q selected
    | true =>
      simp only [d255327, d256986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255328 q = 0) : d256987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255328, d256987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255328, d256987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255329 q = 0) : d256988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255329, d256988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255329, d256988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255330 q = 0) : d256989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255330, d256989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255330, d256989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255331 q = 0) : d256990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255331, d256990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255331, d256990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255332 q = 0) : d256991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255332, d256991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255332, d256991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26119 (p : Pattern) (selected : d255334 p = 0) : d256896 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 0) : d13 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d13, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 0) : d52107 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d52107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254078 q = 0) : d255849 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d254078, d255849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254078, d255849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255334 q = 0) : d256896 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d255334, d256896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255334, d256896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro26120 (p : Pattern) (selected : d255341 p = 0) : d256903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255335 q = 0) : d256897 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d255335, d256897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255335, d256897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26119 q selected
  have h2 (q : Pattern) (selected : d255336 q = 0) : d256898 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d255336, d256898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255336, d256898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
  have h3 (q : Pattern) (selected : d255337 q = 0) : d256899 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d255337, d256899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255337, d256899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255338 q = 0) : d256900 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d255338, d256900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255338, d256900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255339 q = 0) : d256901 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d255339, d256901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255339, d256901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255340 q = 0) : d256902 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d255340, d256902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255340, d256902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255341 q = 0) : d256903 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d255341, d256903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255341, d256903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro26121 (p : Pattern) (selected : d255347 p = 0) : d256909 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255335 q = 0) : d256897 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d255335, d256897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255335, d256897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26119 q selected
  have h2 (q : Pattern) (selected : d255336 q = 0) : d256898 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d255336, d256898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255336, d256898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25968 q selected
  have h3 (q : Pattern) (selected : d255337 q = 0) : d256899 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d255337, d256899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255337, d256899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255338 q = 0) : d256900 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d255338, d256900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255338, d256900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255339 q = 0) : d256901 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d255339, d256901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255339, d256901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255340 q = 0) : d256902 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d255340, d256902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255340, d256902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255347 q = 0) : d256909 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d255347, d256909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255347, d256909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro26122 (p : Pattern) (selected : d255353 p = 0) : d256915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255342 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255342, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26120 q selected
    | true =>
      simp only [d255342, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255343 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255343, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255343, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255344 q = 0) : d256906 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255344, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255344, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255345 q = 0) : d256907 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255345, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255345, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255346 q = 0) : d256908 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255346, d256908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255346, d256908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255348 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
    | true =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255349 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255350 q = 0) : d256912 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255350, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255350, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255351 q = 0) : d256913 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255351, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255351, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d255352 q = 0) : d256914 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255352, d256914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255352, d256914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255353 q = 0) : d256915 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255353, d256915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255353, d256915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26123 (p : Pattern) (selected : d255355 p = 0) : d256917 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255342 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255342, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26120 q selected
    | true =>
      simp only [d255342, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255343 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255343, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255343, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255344 q = 0) : d256906 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255344, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255344, d256906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255345 q = 0) : d256907 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255345, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255345, d256907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255348 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
    | true =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255349 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255350 q = 0) : d256912 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255350, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255350, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255351 q = 0) : d256913 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255351, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255351, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255352 q = 0) : d256914 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255352, d256914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255352, d256914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255354 q = 0) : d256916 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255354, d256916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255354, d256916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255355 q = 0) : d256917 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255355, d256917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255355, d256917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26124 (p : Pattern) (selected : d255359 p = 0) : d256921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255348 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
    | true =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255349 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255350 q = 0) : d256912 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255350, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255350, d256912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255351 q = 0) : d256913 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255351, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255351, d256913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255354 q = 0) : d256916 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255354, d256916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255354, d256916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255359 q = 0) : d256921 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255359, d256921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255359, d256921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26125 (p : Pattern) (selected : d255366 p = 0) : d256928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255356 q = 0) : d256918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255356, d256918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26122 q selected
    | true =>
      simp only [d255356, d256918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26123 q selected
  have h2 (q : Pattern) (selected : d255357 q = 0) : d256919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255357, d256919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255357, d256919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255358 q = 0) : d256920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255358, d256920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255358, d256920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255360 q = 0) : d256922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255360, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26123 q selected
    | true =>
      simp only [d255360, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26124 q selected
  have h5 (q : Pattern) (selected : d255361 q = 0) : d256923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255361, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255361, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255362 q = 0) : d256924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255362, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255362, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255363 q = 0) : d256925 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255363, d256925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255363, d256925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255364 q = 0) : d256926 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255364, d256926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255364, d256926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255365 q = 0) : d256927 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255365, d256927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255365, d256927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255366 q = 0) : d256928 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255366, d256928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255366, d256928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26126 (p : Pattern) (selected : d255370 p = 0) : d256932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255360 q = 0) : d256922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255360, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26123 q selected
    | true =>
      simp only [d255360, d256922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26124 q selected
  have h2 (q : Pattern) (selected : d255361 q = 0) : d256923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255361, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255361, d256923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255362 q = 0) : d256924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255362, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255362, d256924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255364 q = 0) : d256926 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255364, d256926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255364, d256926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255369 q = 0) : d256931 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255369, d256931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255369, d256931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255370 q = 0) : d256932 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255370, d256932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255370, d256932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26127 (p : Pattern) (selected : d255376 p = 0) : d256938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255367 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255367, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26125 q selected
    | true =>
      simp only [d255367, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255368 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255368, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255368, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255371 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255371, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26126 q selected
    | true =>
      simp only [d255371, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255372 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255372, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255372, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255373 q = 0) : d256935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255373, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255373, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255374 q = 0) : d256936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255374, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255374, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255375 q = 0) : d256937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255375, d256937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255375, d256937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255376 q = 0) : d256938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255376, d256938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255376, d256938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26128 (p : Pattern) (selected : d255380 p = 0) : d256942 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255371 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255371, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26126 q selected
    | true =>
      simp only [d255371, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255372 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255372, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255372, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255377 q = 0) : d256939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255377, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255377, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255378 q = 0) : d256940 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255378, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255378, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255379 q = 0) : d256941 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255379, d256941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255379, d256941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255380 q = 0) : d256942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255380, d256942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255380, d256942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26129 (p : Pattern) (selected : d255386 p = 0) : d256997 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255383 q = 0) : d256994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255383, d256994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255383, d256994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255384 q = 0) : d256995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255384, d256995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255384, d256995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255385 q = 0) : d256996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255385, d256996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255385, d256996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255386 q = 0) : d256997 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255386, d256997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255386, d256997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26130 (p : Pattern) (selected : d255392 p = 0) : d257003 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255307 q = 0) : d256966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255307, d256966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26112 q selected
    | true =>
      simp only [d255307, d256966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26113 q selected
  have h2 (q : Pattern) (selected : d255308 q = 0) : d256967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255308, d256967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255308, d256967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255309 q = 0) : d256968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255309, d256968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255309, d256968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255310 q = 0) : d256969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255310, d256969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255310, d256969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255317 q = 0) : d256976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255317, d256976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26114 q selected
    | true =>
      simp only [d255317, d256976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26115 q selected
  have h6 (q : Pattern) (selected : d255318 q = 0) : d256977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255318, d256977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255318, d256977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255319 q = 0) : d256978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255319, d256978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255319, d256978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255333 q = 0) : d256992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255333, d256992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26118 q selected
    | true =>
      simp only [d255333, d256992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26106 q selected
  have h9 (q : Pattern) (selected : d255381 q = 0) : d256943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255381, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26127 q selected
    | true =>
      simp only [d255381, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26128 q selected
  have h10 (q : Pattern) (selected : d255382 q = 0) : d256993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255382, d256993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255382, d256993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255387 q = 0) : d256998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255387, d256998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26129 q selected
    | true =>
      simp only [d255387, d256998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d255388 q = 0) : d256999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255388, d256999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255388, d256999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255389 q = 0) : d257000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255389, d257000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255389, d257000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255390 q = 0) : d257001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255390, d257001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255390, d257001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d255391 q = 0) : d257002 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255391, d257002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255391, d257002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d255392 q = 0) : d257003 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255392, d257003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255392, d257003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro26131 (p : Pattern) (selected : d255393 p = 0) : d257004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255276 q = 0) : d256935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255277 q = 0) : d256936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255277, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255277, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255303 q = 0) : d256962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255303, d256962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255303, d256962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255393 q = 0) : d257004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255393, d257004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255393, d257004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26132 (p : Pattern) (selected : d255394 p = 0) : d257005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255280 q = 0) : d256939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255281 q = 0) : d256940 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255281, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255281, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255305 q = 0) : d256964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255305, d256964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255305, d256964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255394 q = 0) : d257005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255394, d257005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255394, d257005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26133 (p : Pattern) (selected : d255399 p = 0) : d257010 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255276 q = 0) : d256935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255276, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255311 q = 0) : d256970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255311, d256970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255311, d256970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255312 q = 0) : d256971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255312, d256971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255312, d256971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255399 q = 0) : d257010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255399, d257010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255399, d257010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26134 (p : Pattern) (selected : d255400 p = 0) : d257011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255274 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26105 q selected
    | true =>
      simp only [d255274, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255275 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255275, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255280 q = 0) : d256939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255280, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255314 q = 0) : d256973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255314, d256973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255314, d256973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255315 q = 0) : d256974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255315, d256974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255315, d256974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255400 q = 0) : d257011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255400, d257011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255400, d257011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26135 (p : Pattern) (selected : d255404 p = 0) : d257015 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255327 q = 0) : d256986 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255327, d256986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26117 q selected
    | true =>
      simp only [d255327, d256986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255328 q = 0) : d256987 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255328, d256987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255328, d256987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255329 q = 0) : d256988 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255329, d256988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255329, d256988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255330 q = 0) : d256989 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255330, d256989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255330, d256989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255331 q = 0) : d256990 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255331, d256990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255331, d256990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255404 q = 0) : d257015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255404, d257015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255404, d257015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26136 (p : Pattern) (selected : d255406 p = 0) : d256951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255367 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255367, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26125 q selected
    | true =>
      simp only [d255367, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255368 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255368, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255368, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255371 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255371, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26126 q selected
    | true =>
      simp only [d255371, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255372 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255372, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255372, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255373 q = 0) : d256935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255373, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255373, d256935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255374 q = 0) : d256936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255374, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255374, d256936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255375 q = 0) : d256937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255375, d256937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255375, d256937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255406 q = 0) : d256951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255406, d256951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255406, d256951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26137 (p : Pattern) (selected : d255407 p = 0) : d256952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255371 q = 0) : d256933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255371, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26126 q selected
    | true =>
      simp only [d255371, d256933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255372 q = 0) : d256934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255372, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255372, d256934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255377 q = 0) : d256939 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255377, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255377, d256939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255378 q = 0) : d256940 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255378, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255378, d256940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255379 q = 0) : d256941 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255379, d256941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255379, d256941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255407 q = 0) : d256952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255407, d256952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255407, d256952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26138 (p : Pattern) (selected : d255410 p = 0) : d257018 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255270 q = 0) : d256929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26104 q selected
    | true =>
      simp only [d255270, d256929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255271 q = 0) : d256930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255271, d256930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255383 q = 0) : d256994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255383, d256994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255383, d256994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255384 q = 0) : d256995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255384, d256995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255384, d256995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255385 q = 0) : d256996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255385, d256996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255385, d256996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255410 q = 0) : d257018 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255410, d257018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255410, d257018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26139 (p : Pattern) (selected : d255416 p = 0) : d257024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255307 q = 0) : d256966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255307, d256966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26112 q selected
    | true =>
      simp only [d255307, d256966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26113 q selected
  have h2 (q : Pattern) (selected : d255308 q = 0) : d256967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255308, d256967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255308, d256967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255309 q = 0) : d256968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255309, d256968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255309, d256968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255310 q = 0) : d256969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255310, d256969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255310, d256969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255317 q = 0) : d256976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255317, d256976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26114 q selected
    | true =>
      simp only [d255317, d256976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26115 q selected
  have h6 (q : Pattern) (selected : d255318 q = 0) : d256977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255318, d256977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255318, d256977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255319 q = 0) : d256978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255319, d256978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255319, d256978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255333 q = 0) : d256992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255333, d256992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26118 q selected
    | true =>
      simp only [d255333, d256992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26106 q selected
  have h9 (q : Pattern) (selected : d255381 q = 0) : d256943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255381, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26127 q selected
    | true =>
      simp only [d255381, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26128 q selected
  have h10 (q : Pattern) (selected : d255382 q = 0) : d256993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255382, d256993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255382, d256993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255387 q = 0) : d256998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255387, d256998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26129 q selected
    | true =>
      simp only [d255387, d256998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d255388 q = 0) : d256999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255388, d256999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255388, d256999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255389 q = 0) : d257000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255389, d257000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255389, d257000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255390 q = 0) : d257001 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255390, d257001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255390, d257001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d255391 q = 0) : d257002 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255391, d257002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255391, d257002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d255395 q = 0) : d257006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255395, d257006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26131 q selected
    | true =>
      simp only [d255395, d257006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26132 q selected
  have h17 (q : Pattern) (selected : d255396 q = 0) : d257007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255396, d257007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255396, d257007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d255397 q = 0) : d257008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255397, d257008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d255397, d257008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d255398 q = 0) : d257009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255398, d257009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255398, d257009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d255401 q = 0) : d257012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255401, d257012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26133 q selected
    | true =>
      simp only [d255401, d257012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26134 q selected
  have h21 (q : Pattern) (selected : d255402 q = 0) : d257013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255402, d257013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255402, d257013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d255403 q = 0) : d257014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255403, d257014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d255403, d257014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d255405 q = 0) : d257016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255405, d257016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26135 q selected
    | true =>
      simp only [d255405, d257016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26109 q selected
  have h24 (q : Pattern) (selected : d255408 q = 0) : d256953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255408, d256953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26136 q selected
    | true =>
      simp only [d255408, d256953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26137 q selected
  have h25 (q : Pattern) (selected : d255409 q = 0) : d257017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255409, d257017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d255409, d257017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d255411 q = 0) : d257019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255411, d257019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26138 q selected
    | true =>
      simp only [d255411, d257019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d255412 q = 0) : d257020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255412, d257020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d255412, d257020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d255413 q = 0) : d257021 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255413, d257021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d255413, d257021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d255414 q = 0) : d257022 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255414, d257022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d255414, d257022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d255415 q = 0) : d257023 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255415, d257023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d255415, d257023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d255416 q = 0) : d257024 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255416, d257024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d255416, d257024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro26140 (p : Pattern) (selected : d255423 p = 0) : d257031 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255284 q = 0) : d256943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255284, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26106 q selected
    | true =>
      simp only [d255284, d256943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26107 q selected
  have h2 (q : Pattern) (selected : d255285 q = 0) : d256944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255285, d256944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255285, d256944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255286 q = 0) : d256945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255286, d256945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255286, d256945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255287 q = 0) : d256946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255287, d256946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255287, d256946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255288 q = 0) : d256947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255288, d256947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255288, d256947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255418 q = 0) : d257026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255418, d257026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26107 q selected
    | true =>
      simp only [d255418, d257026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255419 q = 0) : d257027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255419, d257027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255419, d257027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255420 q = 0) : d257028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255420, d257028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255420, d257028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255421 q = 0) : d257029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255421, d257029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255421, d257029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255422 q = 0) : d257030 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255422, d257030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255422, d257030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255423 q = 0) : d257031 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255423, d257031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255423, d257031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26141 (p : Pattern) (selected : d255429 p = 0) : d257037 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255418 q = 0) : d257026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255418, d257026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26107 q selected
    | true =>
      simp only [d255418, d257026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255419 q = 0) : d257027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255419, d257027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255419, d257027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255420 q = 0) : d257028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255420, d257028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255420, d257028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255421 q = 0) : d257029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255421, d257029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255421, d257029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255422 q = 0) : d257030 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255422, d257030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255422, d257030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255424 q = 0) : d257032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255424, d257032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26110 q selected
    | true =>
      simp only [d255424, d257032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255425 q = 0) : d257033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255425, d257033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255425, d257033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255426 q = 0) : d257034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255426, d257034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255426, d257034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255427 q = 0) : d257035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255427, d257035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255427, d257035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255428 q = 0) : d257036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255428, d257036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255428, d257036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255429 q = 0) : d257037 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255429, d257037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255429, d257037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26142 (p : Pattern) (selected : d255436 p = 0) : d257044 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255405 q = 0) : d257016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255405, d257016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26135 q selected
    | true =>
      simp only [d255405, d257016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26109 q selected
  have h2 (q : Pattern) (selected : d255408 q = 0) : d256953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255408, d256953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26136 q selected
    | true =>
      simp only [d255408, d256953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26137 q selected
  have h3 (q : Pattern) (selected : d255409 q = 0) : d257017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255409, d257017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255409, d257017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255411 q = 0) : d257019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255411, d257019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26138 q selected
    | true =>
      simp only [d255411, d257019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255412 q = 0) : d257020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255412, d257020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255412, d257020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255413 q = 0) : d257021 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255413, d257021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255413, d257021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255434 q = 0) : d257042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255434, d257042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255434, d257042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255435 q = 0) : d257043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255435, d257043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255435, d257043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255436 q = 0) : d257044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255436, d257044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255436, d257044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro26143 (p : Pattern) (selected : d255438 p = 0) : d257046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255424 q = 0) : d257032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255424, d257032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26110 q selected
    | true =>
      simp only [d255424, d257032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255425 q = 0) : d257033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255425, d257033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255425, d257033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255426 q = 0) : d257034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255426, d257034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255426, d257034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255427 q = 0) : d257035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255427, d257035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255427, d257035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255428 q = 0) : d257036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255428, d257036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255428, d257036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255438 q = 0) : d257046 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255438, d257046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255438, d257046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26144 (p : Pattern) (selected : d255449 p = 0) : d257057 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255444 q = 0) : d257052 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255444, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255444, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
  have h2 (q : Pattern) (selected : d255245 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
    | true =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255445 q = 0) : d257053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255445, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255445, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255246 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255446 q = 0) : d257054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255446, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255446, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255447 q = 0) : d257055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255447, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255447, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255448 q = 0) : d257056 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255448, d257056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255448, d257056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255449 q = 0) : d257057 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255449, d257057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255449, d257057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26145 (p : Pattern) (selected : d255455 p = 0) : d257063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255444 q = 0) : d257052 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255444, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255444, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
  have h2 (q : Pattern) (selected : d255245 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
    | true =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255445 q = 0) : d257053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255445, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255445, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255246 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255446 q = 0) : d257054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255446, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255446, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255447 q = 0) : d257055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255447, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255447, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255448 q = 0) : d257056 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255448, d257056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255448, d257056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255450 q = 0) : d257058 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255450, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255450, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
  have h9 (q : Pattern) (selected : d255251 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
    | true =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d255451 q = 0) : d257059 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255451, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255451, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255252 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d255452 q = 0) : d257060 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255452, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255452, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d255453 q = 0) : d257061 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255453, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255453, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d255454 q = 0) : d257062 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255454, d257062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255454, d257062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d255455 q = 0) : d257063 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255455, d257063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255455, d257063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26146 (p : Pattern) (selected : d255460 p = 0) : d257068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255444 q = 0) : d257052 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255444, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255444, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
  have h2 (q : Pattern) (selected : d255245 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26099 q selected
    | true =>
      simp only [d255245, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255445 q = 0) : d257053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255445, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255445, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255246 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255246, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255446 q = 0) : d257054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255446, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255446, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255447 q = 0) : d257055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255447, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255447, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255450 q = 0) : d257058 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255450, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255450, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
  have h8 (q : Pattern) (selected : d255251 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
    | true =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255451 q = 0) : d257059 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255451, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255451, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255252 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255452 q = 0) : d257060 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255452, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255452, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255453 q = 0) : d257061 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255453, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255453, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255454 q = 0) : d257062 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255454, d257062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255454, d257062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255459 q = 0) : d257067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255459, d257067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255459, d257067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d255460 q = 0) : d257068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255460, d257068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255460, d257068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26147 (p : Pattern) (selected : d255465 p = 0) : d257073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255450 q = 0) : d257058 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255450, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255450, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
  have h2 (q : Pattern) (selected : d255251 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26100 q selected
    | true =>
      simp only [d255251, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255451 q = 0) : d257059 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255451, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255451, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255252 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255252, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255452 q = 0) : d257060 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255452, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255452, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255453 q = 0) : d257061 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255453, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255453, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255459 q = 0) : d257067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255459, d257067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255459, d257067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255465 q = 0) : d257073 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255465, d257073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255465, d257073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26148 (p : Pattern) (selected : d255471 p = 0) : d257079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255456 q = 0) : d257064 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255456, d257064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26144 q selected
    | true =>
      simp only [d255456, d257064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26145 q selected
  have h2 (q : Pattern) (selected : d255457 q = 0) : d257065 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255457, d257065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255457, d257065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255458 q = 0) : d257066 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255458, d257066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255458, d257066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255461 q = 0) : d257069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255461, d257069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26145 q selected
    | true =>
      simp only [d255461, d257069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26146 q selected
  have h5 (q : Pattern) (selected : d255462 q = 0) : d257070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255462, d257070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255462, d257070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255463 q = 0) : d257071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255463, d257071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255463, d257071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255464 q = 0) : d257072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255464, d257072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255464, d257072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255466 q = 0) : d257074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255466, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26146 q selected
    | true =>
      simp only [d255466, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26147 q selected
  have h9 (q : Pattern) (selected : d255467 q = 0) : d257075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255467, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255467, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255468 q = 0) : d257076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255468, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255468, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255469 q = 0) : d257077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255469, d257077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255469, d257077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255470 q = 0) : d257078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255470, d257078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255470, d257078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d255471 q = 0) : d257079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255471, d257079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255471, d257079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro26149 (p : Pattern) (selected : d255476 p = 0) : d257084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255461 q = 0) : d257069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255461, d257069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26145 q selected
    | true =>
      simp only [d255461, d257069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26146 q selected
  have h2 (q : Pattern) (selected : d255462 q = 0) : d257070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255462, d257070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255462, d257070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255463 q = 0) : d257071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255463, d257071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255463, d257071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255466 q = 0) : d257074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255466, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26146 q selected
    | true =>
      simp only [d255466, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26147 q selected
  have h5 (q : Pattern) (selected : d255467 q = 0) : d257075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255467, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255467, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255468 q = 0) : d257076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255468, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255468, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255469 q = 0) : d257077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255469, d257077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255469, d257077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255474 q = 0) : d257082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255474, d257082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255474, d257082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255475 q = 0) : d257083 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255475, d257083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255475, d257083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255476 q = 0) : d257084 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255476, d257084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255476, d257084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26150 (p : Pattern) (selected : d255482 p = 0) : d257090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255472 q = 0) : d257080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255472, d257080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26148 q selected
    | true =>
      simp only [d255472, d257080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255473 q = 0) : d257081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255473, d257081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255473, d257081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255477 q = 0) : d257085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255477, d257085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26149 q selected
    | true =>
      simp only [d255477, d257085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255478 q = 0) : d257086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255478, d257086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255478, d257086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255479 q = 0) : d257087 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255479, d257087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255479, d257087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255480 q = 0) : d257088 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255480, d257088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255480, d257088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255481 q = 0) : d257089 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255481, d257089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255481, d257089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255482 q = 0) : d257090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255482, d257090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255482, d257090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26151 (p : Pattern) (selected : d255484 p = 0) : d257092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255466 q = 0) : d257074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255466, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26146 q selected
    | true =>
      simp only [d255466, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26147 q selected
  have h2 (q : Pattern) (selected : d255467 q = 0) : d257075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255467, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255467, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255468 q = 0) : d257076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255468, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255468, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255474 q = 0) : d257082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255474, d257082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255474, d257082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255483 q = 0) : d257091 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255483, d257091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255483, d257091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255484 q = 0) : d257092 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255484, d257092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255484, d257092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26152 (p : Pattern) (selected : d255490 p = 0) : d257098 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255477 q = 0) : d257085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255477, d257085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26149 q selected
    | true =>
      simp only [d255477, d257085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255478 q = 0) : d257086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255478, d257086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255478, d257086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255485 q = 0) : d257093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255485, d257093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26151 q selected
    | true =>
      simp only [d255485, d257093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255486 q = 0) : d257094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255486, d257094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255486, d257094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255487 q = 0) : d257095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255487, d257095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255487, d257095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255488 q = 0) : d257096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255488, d257096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255488, d257096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255489 q = 0) : d257097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255489, d257097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255489, d257097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255490 q = 0) : d257098 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255490, d257098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255490, d257098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26153 (p : Pattern) (selected : d255502 p = 0) : d257063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255492 q = 0) : d257052 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255492, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255492, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26120 q selected
  have h2 (q : Pattern) (selected : d255342 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255342, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26120 q selected
    | true =>
      simp only [d255342, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255493 q = 0) : d257053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255493, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255493, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255343 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255343, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255343, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255494 q = 0) : d257054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255494, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255494, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255495 q = 0) : d257055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255495, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255495, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255496 q = 0) : d257056 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255496, d257056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255496, d257056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255497 q = 0) : d257058 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255497, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255497, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
  have h9 (q : Pattern) (selected : d255348 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
    | true =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d255498 q = 0) : d257059 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255498, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255498, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255349 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d255499 q = 0) : d257060 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255499, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255499, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d255500 q = 0) : d257061 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255500, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255500, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d255501 q = 0) : d257062 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255501, d257062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255501, d257062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d255502 q = 0) : d257063 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255502, d257063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255502, d257063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26154 (p : Pattern) (selected : d255504 p = 0) : d257068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255492 q = 0) : d257052 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255492, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255492, d257052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26120 q selected
  have h2 (q : Pattern) (selected : d255342 q = 0) : d256904 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255342, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26120 q selected
    | true =>
      simp only [d255342, d256904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255493 q = 0) : d257053 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255493, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255493, d257053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255343 q = 0) : d256905 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255343, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255343, d256905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255494 q = 0) : d257054 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255494, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255494, d257054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255495 q = 0) : d257055 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255495, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255495, d257055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255497 q = 0) : d257058 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255497, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255497, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
  have h8 (q : Pattern) (selected : d255348 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
    | true =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255498 q = 0) : d257059 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255498, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255498, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255349 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d255499 q = 0) : d257060 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255499, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255499, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d255500 q = 0) : d257061 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255500, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255500, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d255501 q = 0) : d257062 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255501, d257062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255501, d257062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255503 q = 0) : d257067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255503, d257067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d255503, d257067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d255504 q = 0) : d257068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255504, d257068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255504, d257068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26155 (p : Pattern) (selected : d255508 p = 0) : d257073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255497 q = 0) : d257058 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255497, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255497, d257058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
  have h2 (q : Pattern) (selected : d255348 q = 0) : d256910 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26121 q selected
    | true =>
      simp only [d255348, d256910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255498 q = 0) : d257059 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255498, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255498, d257059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255349 q = 0) : d256911 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255349, d256911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255499 q = 0) : d257060 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d255499, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255499, d257060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255500 q = 0) : d257061 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d255500, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255500, d257061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255503 q = 0) : d257067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d255503, d257067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255503, d257067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255508 q = 0) : d257073 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d255508, d257073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255508, d257073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26156 (p : Pattern) (selected : d255515 p = 0) : d257084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255505 q = 0) : d257069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255505, d257069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26153 q selected
    | true =>
      simp only [d255505, d257069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26154 q selected
  have h2 (q : Pattern) (selected : d255506 q = 0) : d257070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255506, d257070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255506, d257070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255507 q = 0) : d257071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255507, d257071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255507, d257071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255509 q = 0) : d257074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255509, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26154 q selected
    | true =>
      simp only [d255509, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26155 q selected
  have h5 (q : Pattern) (selected : d255510 q = 0) : d257075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255510, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255510, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255511 q = 0) : d257076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255511, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255511, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255512 q = 0) : d257077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255512, d257077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255512, d257077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255513 q = 0) : d257082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255513, d257082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255513, d257082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d255514 q = 0) : d257083 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255514, d257083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255514, d257083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255515 q = 0) : d257084 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255515, d257084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d255515, d257084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26157 (p : Pattern) (selected : d255519 p = 0) : d257092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255509 q = 0) : d257074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d255509, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26154 q selected
    | true =>
      simp only [d255509, d257074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26155 q selected
  have h2 (q : Pattern) (selected : d255510 q = 0) : d257075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d255510, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255510, d257075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255511 q = 0) : d257076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d255511, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255511, d257076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255513 q = 0) : d257082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d255513, d257082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255513, d257082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255518 q = 0) : d257091 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255518, d257091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255518, d257091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255519 q = 0) : d257092 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d255519, d257092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255519, d257092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26158 (p : Pattern) (selected : d255525 p = 0) : d257098 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255516 q = 0) : d257085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255516, d257085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26156 q selected
    | true =>
      simp only [d255516, d257085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255517 q = 0) : d257086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255517, d257086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255517, d257086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255520 q = 0) : d257093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255520, d257093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26157 q selected
    | true =>
      simp only [d255520, d257093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255521 q = 0) : d257094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255521, d257094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255521, d257094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255522 q = 0) : d257095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255522, d257095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255522, d257095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255523 q = 0) : d257096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255523, d257096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255523, d257096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d255524 q = 0) : d257097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255524, d257097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255524, d257097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d255525 q = 0) : d257098 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255525, d257098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d255525, d257098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26159 (p : Pattern) (selected : d255529 p = 0) : d257103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255520 q = 0) : d257093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255520, d257093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26157 q selected
    | true =>
      simp only [d255520, d257093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255521 q = 0) : d257094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255521, d257094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255521, d257094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255526 q = 0) : d257100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255526, d257100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255526, d257100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255527 q = 0) : d257101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255527, d257101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255527, d257101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255528 q = 0) : d257102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255528, d257102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255528, d257102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255529 q = 0) : d257103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255529, d257103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255529, d257103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26160 (p : Pattern) (selected : d255535 p = 0) : d257109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255477 q = 0) : d257085 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255477, d257085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26149 q selected
    | true =>
      simp only [d255477, d257085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255478 q = 0) : d257086 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255478, d257086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255478, d257086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255532 q = 0) : d257106 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255532, d257106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255532, d257106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255533 q = 0) : d257107 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255533, d257107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255533, d257107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255534 q = 0) : d257108 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255534, d257108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255534, d257108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255535 q = 0) : d257109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255535, d257109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255535, d257109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26161 (p : Pattern) (selected : d255541 p = 0) : d257115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255491 q = 0) : d257099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255491, d257099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26150 q selected
    | true =>
      simp only [d255491, d257099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26152 q selected
  have h2 (q : Pattern) (selected : d255530 q = 0) : d257104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255530, d257104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26158 q selected
    | true =>
      simp only [d255530, d257104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26159 q selected
  have h3 (q : Pattern) (selected : d255531 q = 0) : d257105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255531, d257105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255531, d257105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255536 q = 0) : d257110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255536, d257110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26160 q selected
    | true =>
      simp only [d255536, d257110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255537 q = 0) : d257111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255537, d257111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255537, d257111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255538 q = 0) : d257112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255538, d257112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255538, d257112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255539 q = 0) : d257113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255539, d257113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255539, d257113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d255540 q = 0) : d257114 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255540, d257114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255540, d257114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255541 q = 0) : d257115 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255541, d257115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255541, d257115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro26162 (p : Pattern) (selected : d255546 p = 0) : d257103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255485 q = 0) : d257093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d255485, d257093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26151 q selected
    | true =>
      simp only [d255485, d257093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255486 q = 0) : d257094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d255486, d257094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255486, d257094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255543 q = 0) : d257100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d255543, d257100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255543, d257100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255544 q = 0) : d257101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d255544, d257101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255544, d257101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255545 q = 0) : d257102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d255545, d257102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255545, d257102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255546 q = 0) : d257103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d255546, d257103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255546, d257103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26163 (p : Pattern) (selected : d255552 p = 0) : d257122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255547 q = 0) : d257117 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d255547, d257117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26162 q selected
    | true =>
      simp only [d255547, d257117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255548 q = 0) : d257118 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d255548, d257118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255548, d257118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255549 q = 0) : d257119 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d255549, d257119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255549, d257119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255550 q = 0) : d257120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d255550, d257120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255550, d257120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255551 q = 0) : d257121 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d255551, d257121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255551, d257121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255552 q = 0) : d257122 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d255552, d257122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255552, d257122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26164 (p : Pattern) (selected : d255558 p = 0) : d257128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255290 q = 0) : d256949 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255290, d256949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255290, d256949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26108 q selected
  have h2 (q : Pattern) (selected : d255291 q = 0) : d256950 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255291, d256950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255291, d256950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255300 q = 0) : d256959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255300, d256959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26108 q selected
    | true =>
      simp only [d255300, d256959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26111 q selected
  have h4 (q : Pattern) (selected : d255301 q = 0) : d256960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255301, d256960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255301, d256960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255302 q = 0) : d256961 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255302, d256961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255302, d256961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255417 q = 0) : d257025 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255417, d257025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26130 q selected
    | true =>
      simp only [d255417, d257025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26139 q selected
  have h7 (q : Pattern) (selected : d255430 q = 0) : d257038 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255430, d257038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26140 q selected
    | true =>
      simp only [d255430, d257038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26141 q selected
  have h8 (q : Pattern) (selected : d255431 q = 0) : d257039 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255431, d257039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255431, d257039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255432 q = 0) : d257040 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255432, d257040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d255432, d257040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d255433 q = 0) : d257041 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255433, d257041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255433, d257041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255437 q = 0) : d257045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255437, d257045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255437, d257045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26142 q selected
  have h12 (q : Pattern) (selected : d255439 q = 0) : d257047 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255439, d257047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255439, d257047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26143 q selected
  have h13 (q : Pattern) (selected : d255440 q = 0) : d257048 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255440, d257048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d255440, d257048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255441 q = 0) : d257049 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255441, d257049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d255441, d257049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d255442 q = 0) : d257050 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255442, d257050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d255442, d257050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d255443 q = 0) : d257051 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d255443, d257051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255443, d257051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d255542 q = 0) : d257116 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255542, d257116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255542, d257116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26161 q selected
  have h18 (q : Pattern) (selected : d255553 q = 0) : d257123 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d255553, d257123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255553, d257123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26163 q selected
  have h19 (q : Pattern) (selected : d255554 q = 0) : d257124 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d255554, d257124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d255554, d257124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d255555 q = 0) : d257125 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d255555, d257125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d255555, d257125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d255556 q = 0) : d257126 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d255556, d257126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d255556, d257126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d255557 q = 0) : d257127 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d255557, d257127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d255557, d257127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d255558 q = 0) : d257128 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d255558, d257128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d255558, d257128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro26165 (p : Pattern) (selected : d255564 p = 0) : d257134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255559 q = 0) : d257129 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d255559, d257129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255559, d257129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26164 q selected
  have h2 (q : Pattern) (selected : d255560 q = 0) : d257130 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d255560, d257130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255560, d257130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d255561 q = 0) : d257131 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d255561, d257131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255561, d257131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d255562 q = 0) : d257132 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d255562, d257132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255562, d257132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d255563 q = 0) : d257133 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d255563, d257133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255563, d257133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d255564 q = 0) : d257134 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d255564, d257134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d255564, d257134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26166 (p : Pattern) (selected : d255570 p = 0) : d257140 p = 1 := by
  have h0 (q : Pattern) (selected : d253970 q = 0) : d255983 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d253970, d255983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25837 q selected
    | true =>
      simp only [d253970, d255983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25874 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d254296 q = 0) : d256230 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d254296, d256230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254296, d256230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro25937 q selected
  have h3 (q : Pattern) (selected : d254297 q = 0) : d256231 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d254297, d256231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254297, d256231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254771 q = 0) : d256565 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d254771, d256565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254771, d256565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26018 q selected
  have h5 (q : Pattern) (selected : d254772 q = 0) : d256566 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d254772, d256566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254772, d256566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254773 q = 0) : d256567 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d254773, d256567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254773, d256567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d255233 q = 0) : d256892 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d255233, d256892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255233, d256892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26097 q selected
  have h8 (q : Pattern) (selected : d255234 q = 0) : d256893 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d255234, d256893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255234, d256893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d255235 q = 0) : d256894 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d255235, d256894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255235, d256894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d255236 q = 0) : d256895 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d255236, d256895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d255236, d256895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d255565 q = 0) : d257135 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d255565, d257135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255565, d257135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26165 q selected
  have h12 (q : Pattern) (selected : d255566 q = 0) : d257136 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d255566, d257136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255566, d257136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d255567 q = 0) : d257137 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d255567, d257137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255567, d257137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d255568 q = 0) : d257138 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d255568, d257138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255568, d257138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d255569 q = 0) : d257139 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d255569, d257139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d255569, d257139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d255570 q = 0) : d257140 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d255570, d257140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d255570, d257140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro26167 (p : Pattern) (selected : d255576 p = 0) : d257146 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255571 q = 0) : d257141 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d255571, d257141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26166 q selected
    | true =>
      simp only [d255571, d257141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255572 q = 0) : d257142 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d255572, d257142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255572, d257142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255573 q = 0) : d257143 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d255573, d257143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255573, d257143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255574 q = 0) : d257144 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d255574, d257144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255574, d257144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255575 q = 0) : d257145 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d255575, d257145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255575, d257145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255576 q = 0) : d257146 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d255576, d257146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255576, d257146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26168 (p : Pattern) (selected : d255582 p = 0) : d257152 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255577 q = 0) : d257147 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d255577, d257147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26167 q selected
    | true =>
      simp only [d255577, d257147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255578 q = 0) : d257148 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d255578, d257148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255578, d257148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255579 q = 0) : d257149 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d255579, d257149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255579, d257149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255580 q = 0) : d257150 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d255580, d257150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255580, d257150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255581 q = 0) : d257151 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d255581, d257151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255581, d257151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255582 q = 0) : d257152 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d255582, d257152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255582, d257152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26169 (p : Pattern) (selected : d255588 p = 0) : d257158 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255583 q = 0) : d257153 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d255583, d257153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26168 q selected
    | true =>
      simp only [d255583, d257153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255584 q = 0) : d257154 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d255584, d257154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255584, d257154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255585 q = 0) : d257155 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d255585, d257155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255585, d257155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255586 q = 0) : d257156 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d255586, d257156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255586, d257156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255587 q = 0) : d257157 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d255587, d257157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255587, d257157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255588 q = 0) : d257158 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d255588, d257158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255588, d257158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26170 (p : Pattern) (selected : d255594 p = 0) : d257164 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255589 q = 0) : d257159 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d255589, d257159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26169 q selected
    | true =>
      simp only [d255589, d257159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255590 q = 0) : d257160 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d255590, d257160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255590, d257160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255591 q = 0) : d257161 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d255591, d257161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255591, d257161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255592 q = 0) : d257162 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d255592, d257162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255592, d257162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255593 q = 0) : d257163 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d255593, d257163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255593, d257163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255594 q = 0) : d257164 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d255594, d257164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255594, d257164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26171 (p : Pattern) (selected : d255600 p = 0) : d257170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255595 q = 0) : d257165 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d255595, d257165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26170 q selected
    | true =>
      simp only [d255595, d257165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255596 q = 0) : d257166 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d255596, d257166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255596, d257166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255597 q = 0) : d257167 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d255597, d257167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255597, d257167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255598 q = 0) : d257168 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d255598, d257168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255598, d257168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255599 q = 0) : d257169 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d255599, d257169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255599, d257169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255600 q = 0) : d257170 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d255600, d257170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255600, d257170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26172 (p : Pattern) (selected : d255606 p = 0) : d257176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255601 q = 0) : d257171 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d255601, d257171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26171 q selected
    | true =>
      simp only [d255601, d257171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255602 q = 0) : d257172 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d255602, d257172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255602, d257172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255603 q = 0) : d257173 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d255603, d257173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255603, d257173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255604 q = 0) : d257174 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d255604, d257174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255604, d257174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255605 q = 0) : d257175 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d255605, d257175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255605, d257175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255606 q = 0) : d257176 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d255606, d257176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255606, d257176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26173 (p : Pattern) (selected : d255612 p = 0) : d257182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d255607 q = 0) : d257177 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d255607, d257177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26172 q selected
    | true =>
      simp only [d255607, d257177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d255608 q = 0) : d257178 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d255608, d257178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d255608, d257178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d255609 q = 0) : d257179 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d255609, d257179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d255609, d257179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d255610 q = 0) : d257180 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d255610, d257180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d255610, d257180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255611 q = 0) : d257181 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d255611, d257181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255611, d257181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d255612 q = 0) : d257182 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d255612, d257182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d255612, d257182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26174 (p : Pattern) (selected : d253643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d253642 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d253642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d253643 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d253643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro26175 (p : Pattern) (selected : d253649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253646 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253647 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d253647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253648 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d253648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253649 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d253649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26176 (p : Pattern) (selected : d253655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253650 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
    | true =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253651 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253652 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253653 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253654 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d253654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253655 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d253655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26177 (p : Pattern) (selected : d253661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253656 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26176 q selected
    | true =>
      simp only [d253656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253657 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253658 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253659 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d253659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253660 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d253660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253661 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d253661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26178 (p : Pattern) (selected : d253667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26177 q selected
    | true =>
      simp only [d253662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d253664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d253665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d253666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d253667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26179 (p : Pattern) (selected : d253673 p = 1) : d260269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253608 q = 1) : d253608 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253614 q = 1) : d253614 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d253641 q = 1) : d253641 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d253668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26178 q selected
    | true =>
      simp only [d253668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253669 q = 1) : d260265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253669, d260265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253669, d260265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253531 q = 1) : d253531 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d253670 q = 1) : d260266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253670, d260266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253670, d260266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253671 q = 1) : d260267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253671, d260267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253671, d260267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d253672 q = 1) : d260268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253672, d260268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253672, d260268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253673 q = 1) : d260269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d253673, d260269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253673, d260269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro26180 (p : Pattern) (selected : d253685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26177 q selected
    | true =>
      simp only [d253662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d253664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d253665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d253666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d253685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26181 (p : Pattern) (selected : d253691 p = 1) : d260274 p = 1 := by
  have h0 (q : Pattern) (selected : d253608 q = 1) : d253608 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253614 q = 1) : d253614 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253641 q = 1) : d253641 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d253668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26178 q selected
    | true =>
      simp only [d253668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d253669 q = 1) : d260265 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253669, d260265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253669, d260265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253531 q = 1) : d253531 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d253670 q = 1) : d260266 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253670, d260266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253670, d260266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253671 q = 1) : d260267 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253671, d260267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253671, d260267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d253672 q = 1) : d260268 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253672, d260268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253672, d260268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253678 q = 1) : d253678 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d253682 q = 1) : d253682 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d253684 q = 1) : d253684 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d253686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26180 q selected
    | true =>
      simp only [d253686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d253687 q = 1) : d260270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253687, d260270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d253687, d260270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d253538 q = 1) : d253538 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d253688 q = 1) : d260271 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253688, d260271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d253688, d260271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d253689 q = 1) : d260272 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253689, d260272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d253689, d260272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d253690 q = 1) : d260273 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253690, d260273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d253690, d260273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d253691 q = 1) : d260274 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d253691, d260274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253691, d260274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26182 (p : Pattern) (selected : d253700 p = 1) : d260281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253684 q = 1) : d253684 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26180 q selected
    | true =>
      simp only [d253686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253687 q = 1) : d260270 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253687, d260270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253687, d260270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253538 q = 1) : d253538 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d253688 q = 1) : d260271 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253688, d260271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253688, d260271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253698 q = 1) : d260279 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253698, d260279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253698, d260279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253699 q = 1) : d260280 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253699, d260280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253699, d260280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253700 q = 1) : d260281 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d253700, d260281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253700, d260281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26183 (p : Pattern) (selected : d253730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
  have h2 (q : Pattern) (selected : d253650 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
    | true =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253651 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253729 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d253729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253730 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d253730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26184 (p : Pattern) (selected : d253736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253731 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26183 q selected
    | true =>
      simp only [d253731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253732 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253733 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253734 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d253734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253735 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d253735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253736 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d253736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26185 (p : Pattern) (selected : d253742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253737 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26184 q selected
    | true =>
      simp only [d253737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253738 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d253739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d253740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253741 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d253741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d253742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26186 (p : Pattern) (selected : d253748 p = 1) : d260291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253724 q = 1) : d253724 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26185 q selected
    | true =>
      simp only [d253743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253744 q = 1) : d260287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253744, d260287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253744, d260287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253572 q = 1) : d253572 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d253745 q = 1) : d260288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253745, d260288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253745, d260288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253746 q = 1) : d260289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253746, d260289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253746, d260289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253747 q = 1) : d260290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253747, d260290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253747, d260290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253748 q = 1) : d260291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d253748, d260291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253748, d260291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26187 (p : Pattern) (selected : d253754 p = 1) : d260297 p = 1 := by
  have h0 (q : Pattern) (selected : d253602 q = 1) : d253602 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253692 q = 1) : d260275 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d253692, d260275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26179 q selected
    | true =>
      simp only [d253692, d260275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26181 q selected
  have h2 (q : Pattern) (selected : d253694 q = 1) : d253694 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d253695 q = 1) : d260276 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d253695, d260276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253695, d260276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d253696 q = 1) : d260277 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d253696, d260277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253696, d260277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253697 q = 1) : d260278 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d253697, d260278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253697, d260278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253701 q = 1) : d260282 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d253701, d260282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253701, d260282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26182 q selected
  have h8 (q : Pattern) (selected : d253702 q = 1) : d260283 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d253702, d260283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253702, d260283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d253703 q = 1) : d260284 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d253703, d260284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253703, d260284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d253704 q = 1) : d260285 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d253704, d260285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253704, d260285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d253705 q = 1) : d260286 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d253705, d260286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253705, d260286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d253749 q = 1) : d260292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d253749, d260292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253749, d260292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26186 q selected
  have h13 (q : Pattern) (selected : d253750 q = 1) : d260293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d253750, d260293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d253750, d260293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d253751 q = 1) : d260294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d253751, d260294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d253751, d260294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d253752 q = 1) : d260295 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d253752, d260295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d253752, d260295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d253753 q = 1) : d260296 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d253753, d260296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d253753, d260296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d253754 q = 1) : d260297 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d253754, d260297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d253754, d260297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro26188 (p : Pattern) (selected : d253760 p = 1) : d260303 p = 1 := by
  have h0 (q : Pattern) (selected : d253587 q = 1) : d253587 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253755 q = 1) : d260298 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d253755, d260298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253755, d260298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26187 q selected
  have h3 (q : Pattern) (selected : d253756 q = 1) : d260299 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d253756, d260299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253756, d260299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253757 q = 1) : d260300 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d253757, d260300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253757, d260300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d253758 q = 1) : d260301 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d253758, d260301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253758, d260301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253759 q = 1) : d260302 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d253759, d260302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253759, d260302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253760 q = 1) : d260303 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d253760, d260303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253760, d260303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro26189 (p : Pattern) (selected : d253824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253823 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d253823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253642 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d253642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253824 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d253824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26190 (p : Pattern) (selected : d253830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253825 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253826 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253827 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253646 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253828 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d253828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253829 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d253829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253647 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d253647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d253648 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d253648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d253830 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d253830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26191 (p : Pattern) (selected : d253836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26190 q selected
    | true =>
      simp only [d253831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253833 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253834 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253650 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
    | true =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253651 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253652 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253653 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253835 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d253835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253654 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d253654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d253836 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d253836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26192 (p : Pattern) (selected : d253842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26191 q selected
    | true =>
      simp only [d253837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26176 q selected
  have h2 (q : Pattern) (selected : d253838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253656 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26176 q selected
    | true =>
      simp only [d253656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253657 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253658 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253840 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d253840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253659 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d253659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253841 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d253841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253842 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d253842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26193 (p : Pattern) (selected : d253848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253843 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26192 q selected
    | true =>
      simp only [d253843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253844 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26177 q selected
    | true =>
      simp only [d253662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d253845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d253845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d253846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d253847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253848 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d253848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26194 (p : Pattern) (selected : d253860 p = 1) : d260308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253781 q = 1) : d253781 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253787 q = 1) : d253787 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d253822 q = 1) : d253822 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d253849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26193 q selected
    | true =>
      simp only [d253849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26178 q selected
  have h5 (q : Pattern) (selected : d253850 q = 1) : d260304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253850, d260304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253850, d260304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253856 q = 1) : d253856 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d253857 q = 1) : d260305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253857, d260305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253857, d260305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253858 q = 1) : d260306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253858, d260306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253858, d260306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d253859 q = 1) : d260307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253859, d260307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253859, d260307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253860 q = 1) : d260308 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d253860, d260308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253860, d260308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro26195 (p : Pattern) (selected : d253872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253843 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26192 q selected
    | true =>
      simp only [d253843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253844 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26177 q selected
    | true =>
      simp only [d253662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d253845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d253845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d253846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d253847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253872 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d253872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26196 (p : Pattern) (selected : d253881 p = 1) : d260313 p = 1 := by
  have h0 (q : Pattern) (selected : d253781 q = 1) : d253781 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253787 q = 1) : d253787 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253822 q = 1) : d253822 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d253849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26193 q selected
    | true =>
      simp only [d253849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26178 q selected
  have h4 (q : Pattern) (selected : d253850 q = 1) : d260304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253850, d260304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253850, d260304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d253856 q = 1) : d253856 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d253857 q = 1) : d260305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253857, d260305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253857, d260305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253858 q = 1) : d260306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253858, d260306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253858, d260306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253859 q = 1) : d260307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253859, d260307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253859, d260307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d253865 q = 1) : d253865 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d253869 q = 1) : d253869 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d253871 q = 1) : d253871 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d253873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26195 q selected
    | true =>
      simp only [d253873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26180 q selected
  have h13 (q : Pattern) (selected : d253874 q = 1) : d260309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253874, d260309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d253874, d260309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d253877 q = 1) : d253877 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d253878 q = 1) : d260310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253878, d260310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d253878, d260310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d253879 q = 1) : d260311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253879, d260311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d253879, d260311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d253880 q = 1) : d260312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253880, d260312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253880, d260312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d253881 q = 1) : d260313 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d253881, d260313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253881, d260313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro26197 (p : Pattern) (selected : d253890 p = 1) : d260320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253871 q = 1) : d253871 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26195 q selected
    | true =>
      simp only [d253873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26180 q selected
  have h3 (q : Pattern) (selected : d253874 q = 1) : d260309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253874, d260309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253874, d260309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253877 q = 1) : d253877 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d253878 q = 1) : d260310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253878, d260310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253878, d260310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253888 q = 1) : d260318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253888, d260318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253888, d260318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253889 q = 1) : d260319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253889, d260319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253889, d260319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253890 q = 1) : d260320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d253890, d260320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253890, d260320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26198 (p : Pattern) (selected : d253927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253922 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26190 q selected
  have h2 (q : Pattern) (selected : d253831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26190 q selected
    | true =>
      simp only [d253831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253923 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253924 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253925 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
  have h8 (q : Pattern) (selected : d253650 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
    | true =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253651 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d253727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d253728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d253728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d253926 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d253926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d253729 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d253729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d253729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d253927 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d253927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d253927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26199 (p : Pattern) (selected : d253933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253928 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26198 q selected
    | true =>
      simp only [d253928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26183 q selected
  have h2 (q : Pattern) (selected : d253929 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253930 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253731 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26183 q selected
    | true =>
      simp only [d253731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253732 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253733 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253931 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d253931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253734 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d253734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253932 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d253932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253933 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d253933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26200 (p : Pattern) (selected : d253939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253934 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26199 q selected
    | true =>
      simp only [d253934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253935 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253737 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d253737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26184 q selected
    | true =>
      simp only [d253737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253738 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d253738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d253936 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d253936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253937 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d253937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253938 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d253938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253939 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d253939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26201 (p : Pattern) (selected : d253951 p = 1) : d260330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253921 q = 1) : d253921 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d253940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d253940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26200 q selected
    | true =>
      simp only [d253940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26185 q selected
  have h3 (q : Pattern) (selected : d253941 q = 1) : d260326 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d253941, d260326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253941, d260326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253947 q = 1) : d253947 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d253948 q = 1) : d260327 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d253948, d260327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253948, d260327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253949 q = 1) : d260328 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d253949, d260328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253949, d260328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253950 q = 1) : d260329 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d253950, d260329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253950, d260329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253951 q = 1) : d260330 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d253951, d260330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253951, d260330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26202 (p : Pattern) (selected : d253963 p = 1) : d260336 p = 1 := by
  have h0 (q : Pattern) (selected : d253775 q = 1) : d253775 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253882 q = 1) : d260314 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d253882, d260314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26194 q selected
    | true =>
      simp only [d253882, d260314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26196 q selected
  have h2 (q : Pattern) (selected : d253884 q = 1) : d253884 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d253885 q = 1) : d260315 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d253885, d260315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253885, d260315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d253886 q = 1) : d260316 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d253886, d260316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253886, d260316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253887 q = 1) : d260317 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d253887, d260317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253887, d260317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d253891 q = 1) : d260321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d253891, d260321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253891, d260321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26197 q selected
  have h8 (q : Pattern) (selected : d253893 q = 1) : d253893 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d253894 q = 1) : d260322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d253894, d260322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253894, d260322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253895 q = 1) : d260323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d253895, d260323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253895, d260323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d253896 q = 1) : d260324 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d253896, d260324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d253896, d260324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d253897 q = 1) : d260325 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d253897, d260325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253897, d260325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d253952 q = 1) : d260331 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d253952, d260331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253952, d260331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26201 q selected
  have h14 (q : Pattern) (selected : d253958 q = 1) : d253958 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d253959 q = 1) : d260332 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d253959, d260332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d253959, d260332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d253960 q = 1) : d260333 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d253960, d260333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d253960, d260333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d253961 q = 1) : d260334 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d253961, d260334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d253961, d260334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d253962 q = 1) : d260335 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d253962, d260335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d253962, d260335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d253963 q = 1) : d260336 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d253963, d260336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d253963, d260336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26203 (p : Pattern) (selected : d253969 p = 1) : d260342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253964 q = 1) : d260337 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d253964, d260337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253964, d260337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26202 q selected
  have h2 (q : Pattern) (selected : d253965 q = 1) : d260338 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d253965, d260338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253965, d260338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253966 q = 1) : d260339 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d253966, d260339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253966, d260339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253967 q = 1) : d260340 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d253967, d260340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253967, d260340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d253968 q = 1) : d260341 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d253968, d260341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253968, d260341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253969 q = 1) : d260342 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d253969, d260342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253969, d260342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26204 (p : Pattern) (selected : d254079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254078 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d254078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d158 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d159 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253823 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d253823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254079 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d254079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26205 (p : Pattern) (selected : d254085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26204 q selected
    | true =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253825 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253826 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253827 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254083 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254084 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d253646 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d253828 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d253828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d253829 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d253829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d253829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d254085 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro26206 (p : Pattern) (selected : d254093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253825 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d253826 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253827 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254091 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254092 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253646 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253647 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d253647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d253648 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d253648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254093 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26207 (p : Pattern) (selected : d254099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26205 q selected
    | true =>
      simp only [d254086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d253831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26190 q selected
    | true =>
      simp only [d253831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d253832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d253832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253833 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d253834 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254090 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254094 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26206 q selected
    | true =>
      simp only [d254094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254095 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254096 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254097 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d253650 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
    | true =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d253651 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d253652 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d253653 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d253653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254098 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254099 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26208 (p : Pattern) (selected : d254106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254100 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26207 q selected
    | true =>
      simp only [d254100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26191 q selected
  have h2 (q : Pattern) (selected : d254101 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254102 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26191 q selected
    | true =>
      simp only [d253837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26176 q selected
  have h5 (q : Pattern) (selected : d253838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254103 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254104 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254105 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254106 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26209 (p : Pattern) (selected : d254110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253837 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26191 q selected
    | true =>
      simp only [d253837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26176 q selected
  have h2 (q : Pattern) (selected : d253838 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253839 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254104 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254109 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254110 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26210 (p : Pattern) (selected : d254116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254107 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26208 q selected
    | true =>
      simp only [d254107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254108 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254111 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26209 q selected
    | true =>
      simp only [d254111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254112 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254113 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254114 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254116 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26211 (p : Pattern) (selected : d254120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254111 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26209 q selected
    | true =>
      simp only [d254111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254112 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254117 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254118 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254119 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254120 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26212 (p : Pattern) (selected : d254132 p = 1) : d260348 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254014 q = 1) : d254014 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d254023 q = 1) : d254023 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d254077 q = 1) : d254077 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d254121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26210 q selected
    | true =>
      simp only [d254121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26211 q selected
  have h5 (q : Pattern) (selected : d254122 q = 1) : d260344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254122, d260344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254122, d260344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254128 q = 1) : d254128 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d254129 q = 1) : d260345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254129, d260345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254129, d260345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254130 q = 1) : d260346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254130, d260346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254130, d260346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254131 q = 1) : d260347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254131, d260347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254131, d260347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254132 q = 1) : d260348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254132, d260348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254132, d260348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro26213 (p : Pattern) (selected : d254146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254107 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26208 q selected
    | true =>
      simp only [d254107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254108 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254111 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26209 q selected
    | true =>
      simp only [d254111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254112 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254113 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254114 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254146 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26214 (p : Pattern) (selected : d254147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254111 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26209 q selected
    | true =>
      simp only [d254111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254112 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254117 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254118 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254119 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254147 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26215 (p : Pattern) (selected : d254156 p = 1) : d260353 p = 1 := by
  have h0 (q : Pattern) (selected : d254014 q = 1) : d254014 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254023 q = 1) : d254023 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d254077 q = 1) : d254077 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d254121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26210 q selected
    | true =>
      simp only [d254121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26211 q selected
  have h4 (q : Pattern) (selected : d254122 q = 1) : d260344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254122, d260344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254122, d260344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254128 q = 1) : d254128 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d254129 q = 1) : d260345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254129, d260345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254129, d260345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254130 q = 1) : d260346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254130, d260346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254130, d260346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254131 q = 1) : d260347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254131, d260347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254131, d260347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254138 q = 1) : d254138 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d254143 q = 1) : d254143 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d254145 q = 1) : d254145 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d254148 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26213 q selected
    | true =>
      simp only [d254148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26214 q selected
  have h13 (q : Pattern) (selected : d254149 q = 1) : d260349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254149, d260349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254149, d260349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254152 q = 1) : d254152 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d254153 q = 1) : d260350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254153, d260350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254153, d260350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254154 q = 1) : d260351 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254154, d260351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254154, d260351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254155 q = 1) : d260352 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254155, d260352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254155, d260352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d254156 q = 1) : d260353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254156, d260353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254156, d260353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro26216 (p : Pattern) (selected : d254176 p = 1) : d260360 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254145 q = 1) : d254145 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d254148 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26213 q selected
    | true =>
      simp only [d254148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26214 q selected
  have h3 (q : Pattern) (selected : d254149 q = 1) : d260349 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254149, d260349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254149, d260349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254152 q = 1) : d254152 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d254153 q = 1) : d260350 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254153, d260350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254153, d260350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254174 q = 1) : d260358 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254174, d260358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254174, d260358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254175 q = 1) : d260359 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254175, d260359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254175, d260359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254176 q = 1) : d260360 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254176, d260360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254176, d260360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26217 (p : Pattern) (selected : d254239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254229 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26205 q selected
  have h2 (q : Pattern) (selected : d254086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26205 q selected
    | true =>
      simp only [d254086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254230 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254231 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254232 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253922 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26190 q selected
  have h8 (q : Pattern) (selected : d253831 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26190 q selected
    | true =>
      simp only [d253831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253923 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d253832 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d253924 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d253925 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d253925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254233 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254234 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26206 q selected
  have h15 (q : Pattern) (selected : d254094 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26206 q selected
    | true =>
      simp only [d254094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254235 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254095 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254236 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254237 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d254237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d253725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
  have h21 (q : Pattern) (selected : d253650 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26175 q selected
    | true =>
      simp only [d253650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d253726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d253726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d253651 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d253651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d253727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d253727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d253727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d253728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d253728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d253728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d254238 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d254238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d254239 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro26218 (p : Pattern) (selected : d254246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254240 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26217 q selected
    | true =>
      simp only [d254240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26198 q selected
  have h2 (q : Pattern) (selected : d254241 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254242 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d253928 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26198 q selected
    | true =>
      simp only [d253928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26183 q selected
  have h5 (q : Pattern) (selected : d253929 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253930 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254243 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254244 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254245 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254246 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26219 (p : Pattern) (selected : d254250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d253928 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d253928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26198 q selected
    | true =>
      simp only [d253928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26183 q selected
  have h2 (q : Pattern) (selected : d253929 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d253929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253930 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254244 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254249 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254250 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26220 (p : Pattern) (selected : d254256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254247 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26218 q selected
    | true =>
      simp only [d254247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254248 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254251 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26219 q selected
    | true =>
      simp only [d254251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254252 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254253 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254254 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254255 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254256 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26221 (p : Pattern) (selected : d254260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254251 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26219 q selected
    | true =>
      simp only [d254251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254252 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254257 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254258 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254259 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254260 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26222 (p : Pattern) (selected : d254272 p = 1) : d260370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254228 q = 1) : d254228 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d254261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26220 q selected
    | true =>
      simp only [d254261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26221 q selected
  have h3 (q : Pattern) (selected : d254262 q = 1) : d260366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254262, d260366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254262, d260366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254268 q = 1) : d254268 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d254269 q = 1) : d260367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254269, d260367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254269, d260367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254270 q = 1) : d260368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254270, d260368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254270, d260368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254271 q = 1) : d260369 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254271, d260369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254271, d260369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254272 q = 1) : d260370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254272, d260370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254272, d260370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26223 (p : Pattern) (selected : d254289 p = 1) : d260376 p = 1 := by
  have h0 (q : Pattern) (selected : d254006 q = 1) : d254006 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254157 q = 1) : d260354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254157, d260354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26212 q selected
    | true =>
      simp only [d254157, d260354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26215 q selected
  have h2 (q : Pattern) (selected : d254170 q = 1) : d254170 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d254171 q = 1) : d260355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254171, d260355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254171, d260355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d254172 q = 1) : d260356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d254172, d260356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254172, d260356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254173 q = 1) : d260357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d254173, d260357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254173, d260357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254177 q = 1) : d260361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254177, d260361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254177, d260361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26216 q selected
  have h8 (q : Pattern) (selected : d254179 q = 1) : d254179 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d254180 q = 1) : d260362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254180, d260362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254180, d260362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254181 q = 1) : d260363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d254181, d260363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254181, d260363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d254182 q = 1) : d260364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d254182, d260364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254182, d260364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d254183 q = 1) : d260365 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d254183, d260365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254183, d260365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254273 q = 1) : d260371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d254273, d260371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254273, d260371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26222 q selected
  have h14 (q : Pattern) (selected : d254284 q = 1) : d254284 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d254285 q = 1) : d260372 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d254285, d260372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254285, d260372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254286 q = 1) : d260373 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d254286, d260373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254286, d260373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d254287 q = 1) : d260374 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d254287, d260374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254287, d260374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d254288 q = 1) : d260375 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d254288, d260375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d254288, d260375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d254289 q = 1) : d260376 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d254289, d260376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254289, d260376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26224 (p : Pattern) (selected : d254295 p = 1) : d260382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254290 q = 1) : d260377 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d254290, d260377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254290, d260377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26223 q selected
  have h2 (q : Pattern) (selected : d254291 q = 1) : d260378 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d254291, d260378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254291, d260378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254292 q = 1) : d260379 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d254292, d260379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254292, d260379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254293 q = 1) : d260380 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d254293, d260380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254293, d260380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254294 q = 1) : d260381 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d254294, d260381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254294, d260381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254295 q = 1) : d260382 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d254295, d260382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254295, d260382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26225 (p : Pattern) (selected : d254453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254078 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d254078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254453 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d254453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro26226 (p : Pattern) (selected : d254458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254078 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d254078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254457 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d254457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254458 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d254458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26227 (p : Pattern) (selected : d254461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2 q = 1) : d0 q = 1 := by
    change (2 : Int) = 1 at selected
    omega
  have h2 (q : Pattern) (selected : d338 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254457 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d254457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254461 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d254461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro26228 (p : Pattern) (selected : d254473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254454 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26225 q selected
    | true =>
      simp only [d254454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254455 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26204 q selected
    | true =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254456 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254459 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26226 q selected
    | true =>
      simp only [d254459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254460 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254462 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26227 q selected
    | true =>
      simp only [d254462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254463 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d254464 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254465 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254466 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254467 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
  have h14 (q : Pattern) (selected : d254468 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254469 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254470 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254471 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d254472 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d254472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d254473 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro26229 (p : Pattern) (selected : d254483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26204 q selected
    | true =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254467 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
  have h4 (q : Pattern) (selected : d254468 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254469 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253825 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253826 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d253827 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254478 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254479 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254480 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d254481 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254482 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254483 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro26230 (p : Pattern) (selected : d254491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26204 q selected
    | true =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d253825 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d253826 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254082 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254489 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254490 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254467 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
  have h9 (q : Pattern) (selected : d254468 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254480 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254481 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d254482 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254491 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26231 (p : Pattern) (selected : d254498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d254467 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d254468 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d254480 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253646 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d254496 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254497 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d254498 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h9 p selected
theorem eqIntro26232 (p : Pattern) (selected : d254504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254474 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26228 q selected
    | true =>
      simp only [d254474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254475 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254476 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254477 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254484 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26229 q selected
    | true =>
      simp only [d254484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254485 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254486 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254487 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254488 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254492 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26230 q selected
    | true =>
      simp only [d254492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254493 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d254494 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d254495 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d254499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
    | true =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254503 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254504 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro26233 (p : Pattern) (selected : d254505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254080 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26204 q selected
    | true =>
      simp only [d254080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254081 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254467 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d254467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
  have h4 (q : Pattern) (selected : d254468 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254469 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253825 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26189 q selected
    | true =>
      simp only [d253825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d253826 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d253826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d253644 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26174 q selected
    | true =>
      simp only [d253644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d253645 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d253645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d253827 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d253827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d254478 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254479 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254480 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d254480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d253646 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d253646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254496 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d254496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254497 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d254497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d254505 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d254505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro26234 (p : Pattern) (selected : d254512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254506 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26233 q selected
    | true =>
      simp only [d254506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254507 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254508 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254509 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
    | true =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254510 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254511 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254512 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro26235 (p : Pattern) (selected : d254516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
    | true =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254501 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254502 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254511 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254516 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26236 (p : Pattern) (selected : d254523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254513 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26232 q selected
    | true =>
      simp only [d254513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26234 q selected
  have h2 (q : Pattern) (selected : d254514 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254515 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26234 q selected
    | true =>
      simp only [d254517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26235 q selected
  have h5 (q : Pattern) (selected : d254518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254520 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254521 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254522 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254523 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26237 (p : Pattern) (selected : d254527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26234 q selected
    | true =>
      simp only [d254517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26235 q selected
  have h2 (q : Pattern) (selected : d254518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254521 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254526 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254527 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26238 (p : Pattern) (selected : d254533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254524 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26236 q selected
    | true =>
      simp only [d254524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254525 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26237 q selected
    | true =>
      simp only [d254528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254530 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254531 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254532 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254533 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26239 (p : Pattern) (selected : d254537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26237 q selected
    | true =>
      simp only [d254528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254534 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254535 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254536 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254537 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro26240 (p : Pattern) (selected : d254549 p = 1) : d260389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254392 q = 1) : d254392 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d254401 q = 1) : d254401 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d254452 q = 1) : d254452 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d254538 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26238 q selected
    | true =>
      simp only [d254538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26239 q selected
  have h5 (q : Pattern) (selected : d254539 q = 1) : d260385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254539, d260385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254539, d260385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254545 q = 1) : d254545 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d254546 q = 1) : d260386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254546, d260386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254546, d260386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254547 q = 1) : d260387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254547, d260387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254547, d260387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254548 q = 1) : d260388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254548, d260388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254548, d260388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254549 q = 1) : d260389 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254549, d260389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254549, d260389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro26241 (p : Pattern) (selected : d254563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254524 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26236 q selected
    | true =>
      simp only [d254524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254525 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26237 q selected
    | true =>
      simp only [d254528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254530 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254531 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254532 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254563 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26242 (p : Pattern) (selected : d254564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254528 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d254528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26237 q selected
    | true =>
      simp only [d254528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d254529 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d254529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254534 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d254534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d254535 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d254535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254536 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d254536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d254564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro26243 (p : Pattern) (selected : d254573 p = 1) : d260394 p = 1 := by
  have h0 (q : Pattern) (selected : d254392 q = 1) : d254392 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254401 q = 1) : d254401 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d254452 q = 1) : d254452 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d254538 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26238 q selected
    | true =>
      simp only [d254538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26239 q selected
  have h4 (q : Pattern) (selected : d254539 q = 1) : d260385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254539, d260385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254539, d260385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d254545 q = 1) : d254545 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d254546 q = 1) : d260386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254546, d260386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254546, d260386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254547 q = 1) : d260387 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254547, d260387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254547, d260387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254548 q = 1) : d260388 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254548, d260388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254548, d260388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d254555 q = 1) : d254555 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d254560 q = 1) : d254560 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d254562 q = 1) : d254562 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d254565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26241 q selected
    | true =>
      simp only [d254565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26242 q selected
  have h13 (q : Pattern) (selected : d254566 q = 1) : d260390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254566, d260390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254566, d260390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254569 q = 1) : d254569 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d254570 q = 1) : d260391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254570, d260391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254570, d260391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d254571 q = 1) : d260392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254571, d260392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d254571, d260392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254572 q = 1) : d260393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254572, d260393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254572, d260393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d254573 q = 1) : d260394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254573, d260394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254573, d260394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro26244 (p : Pattern) (selected : d254593 p = 1) : d260401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254562 q = 1) : d254562 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d254565 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d254565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26241 q selected
    | true =>
      simp only [d254565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26242 q selected
  have h3 (q : Pattern) (selected : d254566 q = 1) : d260390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d254566, d260390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254566, d260390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254569 q = 1) : d254569 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d254570 q = 1) : d260391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d254570, d260391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254570, d260391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254591 q = 1) : d260399 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d254591, d260399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254591, d260399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254592 q = 1) : d260400 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d254592, d260400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254592, d260400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254593 q = 1) : d260401 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d254593, d260401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254593, d260401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro26245 (p : Pattern) (selected : d254703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26228 q selected
  have h2 (q : Pattern) (selected : d254474 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26228 q selected
    | true =>
      simp only [d254474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254686 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254475 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254687 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254688 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254689 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26229 q selected
  have h8 (q : Pattern) (selected : d254484 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26229 q selected
    | true =>
      simp only [d254484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254690 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254485 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254691 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254692 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254693 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26230 q selected
  have h15 (q : Pattern) (selected : d254492 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26230 q selected
    | true =>
      simp only [d254492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d254695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d254695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d254493 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d254493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d254696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d254696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d254697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d254697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d254698 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
  have h21 (q : Pattern) (selected : d254499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
    | true =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d254699 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d254699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d254500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d254700 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d254700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d254701 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d254701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d254702 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d254702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d254703 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro26246 (p : Pattern) (selected : d254710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254704 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26233 q selected
  have h2 (q : Pattern) (selected : d254506 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26233 q selected
    | true =>
      simp only [d254506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254705 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254507 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254706 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254707 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254698 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
  have h8 (q : Pattern) (selected : d254499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
    | true =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254699 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d254700 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d254701 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d254701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d254708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d254709 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d254709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d254710 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d254710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro26247 (p : Pattern) (selected : d254714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254698 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
  have h2 (q : Pattern) (selected : d254499 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26231 q selected
    | true =>
      simp only [d254499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d254699 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d254699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254500 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d254500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254700 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d254700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254701 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d254701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d254709 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d254709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d254714 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d254714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro26248 (p : Pattern) (selected : d254721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254711 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26245 q selected
    | true =>
      simp only [d254711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26246 q selected
  have h2 (q : Pattern) (selected : d254712 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254713 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254715 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26246 q selected
    | true =>
      simp only [d254715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26247 q selected
  have h5 (q : Pattern) (selected : d254716 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d254717 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d254718 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254719 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d254720 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d254720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d254721 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d254721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro26249 (p : Pattern) (selected : d254725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d254715 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d254715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26246 q selected
    | true =>
      simp only [d254715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26247 q selected
  have h2 (q : Pattern) (selected : d254716 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d254716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d254717 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d254717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d254717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254719 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d254724 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d254724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d254724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d254725 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d254725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d254725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
