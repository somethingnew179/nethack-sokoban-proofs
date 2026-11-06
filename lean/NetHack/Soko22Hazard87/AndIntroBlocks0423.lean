import NetHack.Soko22Hazard87.AndIntroBlocks0422
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro105750 (p : Pattern) (ha : d46818 p = 1) (hb : d307598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46812 q = 1) (hb : d307593 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, d307593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46812, d307593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105729 q ha hb
  have h2 (q : Pattern) (ha : d46638 q = 1) (hb : d307420 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, d307420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105729 q ha hb
    | true =>
      simp only [d46638, d307420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46813 q = 1) (hb : d307594 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, d307594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46813, d307594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46639 q = 1) (hb : d307421 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, d307421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46639, d307421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46814 q = 1) (hb : d307595 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, d307595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46814, d307595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46815 q = 1) (hb : d307596 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, d307596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46815, d307596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46816 q = 1) (hb : d307597 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, d307597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46816, d307597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46818 q = 1) (hb : d307598 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46818, d307598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46818, d307598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105751 (p : Pattern) (ha : d46824 p = 1) (hb : d307604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46731 q = 1) (hb : d307550 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, d307550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105743 q ha hb
    | true =>
      simp only [d46731, d307550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105713 q ha hb
  have h2 (q : Pattern) (ha : d46732 q = 1) (hb : d307551 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, d307551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46732, d307551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46733 q = 1) (hb : d307552 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, d307552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46733, d307552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46741 q = 1) (hb : d307555 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, d307555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105713 q ha hb
    | true =>
      simp only [d46741, d307555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105714 q ha hb
  have h5 (q : Pattern) (ha : d46742 q = 1) (hb : d307556 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, d307556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46742, d307556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46743 q = 1) (hb : d307557 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, d307557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46743, d307557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46744 q = 1) (hb : d307558 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, d307558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46744, d307558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46819 q = 1) (hb : d307599 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46819, d307599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105749 q ha hb
    | true =>
      simp only [d46819, d307599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105750 q ha hb
  have h9 (q : Pattern) (ha : d46820 q = 1) (hb : d307600 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46820, d307600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46820, d307600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46821 q = 1) (hb : d307601 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46821, d307601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46821, d307601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46822 q = 1) (hb : d307602 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46822, d307602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46822, d307602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46823 q = 1) (hb : d307603 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46823, d307603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46823, d307603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46824 q = 1) (hb : d307604 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46824, d307604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46824, d307604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105752 (p : Pattern) (ha : d46830 p = 1) (hb : d307610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46825 q = 1) (hb : d307605 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46825, d307605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105751 q ha hb
    | true =>
      simp only [d46825, d307605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46826 q = 1) (hb : d307606 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46826, d307606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46826, d307606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46827 q = 1) (hb : d307607 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46827, d307607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46827, d307607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46828 q = 1) (hb : d307608 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46828, d307608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46828, d307608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46829 q = 1) (hb : d307609 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46829, d307609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46829, d307609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46830 q = 1) (hb : d307610 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46830, d307610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46830, d307610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105753 (p : Pattern) (ha : d307616 p = 1) (hb : d321665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46766 q = 1) (hb : d307580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46766, d307580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105747 q ha hb
    | true =>
      simp only [d46766, d307580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105748 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307585 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307586 q = 1) (hb : d321661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307586, d321661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307586, d321661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d46831 q = 1) (hb : d307611 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46831, d307611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105752 q ha hb
    | true =>
      simp only [d46831, d307611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46832 q = 1) (hb : d307612 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46832, d307612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46832, d307612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d307613 q = 1) (hb : d321662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307613, d321662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307613, d321662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307614 q = 1) (hb : d321663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307614, d321663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307614, d321663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307615 q = 1) (hb : d321664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307615, d321664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307615, d321664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307616 q = 1) (hb : d321665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307616, d321665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307616, d321665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro105754 (p : Pattern) (ha : d307629 p = 1) (hb : d321671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46528 q = 1) (hb : d307330 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46528, d307330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46528, d307330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105706 q ha hb
  have h2 (q : Pattern) (ha : d46529 q = 1) (hb : d307331 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46529, d307331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46529, d307331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46538 q = 1) (hb : d307340 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d307340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105706 q ha hb
    | true =>
      simp only [d46538, d307340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105709 q ha hb
  have h4 (q : Pattern) (ha : d46539 q = 1) (hb : d307341 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d307341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46539, d307341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46540 q = 1) (hb : d307342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46540, d307342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46540, d307342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307465 q = 1) (hb : d321649 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307465, d321649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105733 q ha hb
    | true =>
      simp only [d307465, d321649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105740 q ha hb
  have h7 (q : Pattern) (ha : d46700 q = 1) (hb : d307478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46700, d307478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105710 q ha hb
    | true =>
      simp only [d46700, d307478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105711 q ha hb
  have h8 (q : Pattern) (ha : d307479 q = 1) (hb : d321650 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307479, d321650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307479, d321650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d307480 q = 1) (hb : d321651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307480, d321651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307480, d321651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d307481 q = 1) (hb : d321652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307481, d321652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d307481, d321652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307485 q = 1) (hb : d321656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307485, d321656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307485, d321656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105741 q ha hb
  have h12 (q : Pattern) (ha : d46709 q = 1) (hb : d307487 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46709, d307487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46709, d307487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105712 q ha hb
  have h13 (q : Pattern) (ha : d307488 q = 1) (hb : d321657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307488, d321657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d307488, d321657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d307489 q = 1) (hb : d321658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307489, d321658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307489, d321658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d307490 q = 1) (hb : d321659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307490, d321659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d307490, d321659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d307491 q = 1) (hb : d321660 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307491, d321660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307491, d321660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307617 q = 1) (hb : d321666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307617, d321666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307617, d321666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105753 q ha hb
  have h18 (q : Pattern) (ha : d46848 q = 1) (hb : d307624 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46848, d307624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46848, d307624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105717 q ha hb
  have h19 (q : Pattern) (ha : d307625 q = 1) (hb : d321667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307625, d321667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307625, d321667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d307626 q = 1) (hb : d321668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307626, d321668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d307626, d321668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d307627 q = 1) (hb : d321669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307627, d321669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d307627, d321669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d307628 q = 1) (hb : d321670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307628, d321670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d307628, d321670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d307629 q = 1) (hb : d321671 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307629, d321671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307629, d321671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro105755 (p : Pattern) (ha : d307635 p = 1) (hb : d321677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307630 q = 1) (hb : d321672 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307630, d321672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307630, d321672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105754 q ha hb
  have h2 (q : Pattern) (ha : d307631 q = 1) (hb : d321673 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307631, d321673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307631, d321673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307632 q = 1) (hb : d321674 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307632, d321674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307632, d321674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307633 q = 1) (hb : d321675 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307633, d321675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307633, d321675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307634 q = 1) (hb : d321676 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307634, d321676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307634, d321676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307635 q = 1) (hb : d321677 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307635, d321677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307635, d321677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105756 (p : Pattern) (ha : d307931 p = 1) (hb : d358732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d306523 q = 1) (hb : d358080 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306523, d358080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105523 q ha hb
    | true =>
      simp only [d306523, d358080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105570 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306816 q = 1) (hb : d358362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306816, d358362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306816, d358362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105625 q ha hb
  have h3 (q : Pattern) (ha : d306817 q = 1) (hb : d358363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d306817, d358363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d306817, d358363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307210 q = 1) (hb : d358727 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307210, d358727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307210, d358727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105689 q ha hb
  have h5 (q : Pattern) (ha : d307211 q = 1) (hb : d358728 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307211, d358728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307211, d358728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307212 q = 1) (hb : d358729 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307212, d358729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307212, d358729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307636 q = 1) (hb : d321678 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307636, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307636, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105755 q ha hb
  have h8 (q : Pattern) (ha : d307637 q = 1) (hb : d321679 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307637, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307637, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307638 q = 1) (hb : d321680 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307638, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307638, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307639 q = 1) (hb : d358730 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307639, d358730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307639, d358730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307929 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d307930 q = 1) (hb : d358731 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d307930, d358731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307930, d358731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d307931 q = 1) (hb : d358732 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d307931, d358732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307931, d358732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro105757 (p : Pattern) (ha : d307937 p = 1) (hb : d358738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307932 q = 1) (hb : d358733 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d307932, d358733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105756 q ha hb
    | true =>
      simp only [d307932, d358733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307933 q = 1) (hb : d358734 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d307933, d358734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307933, d358734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307934 q = 1) (hb : d358735 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d307934, d358735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307934, d358735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307935 q = 1) (hb : d358736 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d307935, d358736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307935, d358736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307936 q = 1) (hb : d358737 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d307936, d358737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307936, d358737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307937 q = 1) (hb : d358738 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d307937, d358738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307937, d358738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105758 (p : Pattern) (ha : d307943 p = 1) (hb : d358744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307938 q = 1) (hb : d358739 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d307938, d358739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105757 q ha hb
    | true =>
      simp only [d307938, d358739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307939 q = 1) (hb : d358740 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d307939, d358740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307939, d358740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307940 q = 1) (hb : d358741 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d307940, d358741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307940, d358741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307941 q = 1) (hb : d358742 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d307941, d358742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307941, d358742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307942 q = 1) (hb : d358743 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d307942, d358743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307942, d358743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307943 q = 1) (hb : d358744 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d307943, d358744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307943, d358744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105759 (p : Pattern) (ha : d307949 p = 1) (hb : d358750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307944 q = 1) (hb : d358745 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d307944, d358745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105758 q ha hb
    | true =>
      simp only [d307944, d358745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307945 q = 1) (hb : d358746 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d307945, d358746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307945, d358746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307946 q = 1) (hb : d358747 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d307946, d358747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307946, d358747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307947 q = 1) (hb : d358748 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d307947, d358748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307947, d358748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307948 q = 1) (hb : d358749 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d307948, d358749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307948, d358749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307949 q = 1) (hb : d358750 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d307949, d358750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307949, d358750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105760 (p : Pattern) (ha : d307955 p = 1) (hb : d358756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307950 q = 1) (hb : d358751 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d307950, d358751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105759 q ha hb
    | true =>
      simp only [d307950, d358751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307951 q = 1) (hb : d358752 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d307951, d358752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307951, d358752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307952 q = 1) (hb : d358753 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d307952, d358753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307952, d358753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307953 q = 1) (hb : d358754 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d307953, d358754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307953, d358754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307954 q = 1) (hb : d358755 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d307954, d358755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307954, d358755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307955 q = 1) (hb : d358756 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d307955, d358756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307955, d358756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105761 (p : Pattern) (ha : d307961 p = 1) (hb : d358762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307956 q = 1) (hb : d358757 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d307956, d358757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105760 q ha hb
    | true =>
      simp only [d307956, d358757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307957 q = 1) (hb : d358758 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d307957, d358758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307957, d358758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307958 q = 1) (hb : d358759 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d307958, d358759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307958, d358759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307959 q = 1) (hb : d358760 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d307959, d358760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307959, d358760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307960 q = 1) (hb : d358761 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d307960, d358761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307960, d358761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307961 q = 1) (hb : d358762 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d307961, d358762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307961, d358762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105762 (p : Pattern) (ha : d307967 p = 1) (hb : d358768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307962 q = 1) (hb : d358763 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d307962, d358763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105761 q ha hb
    | true =>
      simp only [d307962, d358763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307963 q = 1) (hb : d358764 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d307963, d358764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307963, d358764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307964 q = 1) (hb : d358765 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d307964, d358765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307964, d358765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307965 q = 1) (hb : d358766 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d307965, d358766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307965, d358766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307966 q = 1) (hb : d358767 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d307966, d358767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307966, d358767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307967 q = 1) (hb : d358768 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d307967, d358768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307967, d358768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105763 (p : Pattern) (ha : d307973 p = 1) (hb : d358774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307968 q = 1) (hb : d358769 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d307968, d358769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105762 q ha hb
    | true =>
      simp only [d307968, d358769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307969 q = 1) (hb : d358770 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d307969, d358770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307969, d358770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307970 q = 1) (hb : d358771 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d307970, d358771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307970, d358771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307971 q = 1) (hb : d358772 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d307971, d358772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307971, d358772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307972 q = 1) (hb : d358773 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d307972, d358773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307972, d358773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307973 q = 1) (hb : d358774 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d307973, d358774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307973, d358774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105764 (p : Pattern) (ha : d14 p = 1) (hb : d321910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105234 q ha hb
    | true =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105235 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46928 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46929 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46930 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d321910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105765 (p : Pattern) (ha : d14 p = 1) (hb : d324333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46865 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d324332 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46866 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d324333 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro105766 (p : Pattern) (ha : d14 p = 1) (hb : d326581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d326576 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d326576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105765 q ha hb
    | true =>
      simp only [d326576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105223 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d326577 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d326578 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d326578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105223 q ha hb
    | true =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d46873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d326579 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d326579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d326580 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d326580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d326581 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d326581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro105767 (p : Pattern) (ha : d14 p = 1) (hb : d326587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d47086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105224 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d47087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d47088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d47089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d47095 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d47101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105227 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d46889 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105227 q ha hb
    | true =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d47102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d326582 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105766 q ha hb
    | true =>
      simp only [d326582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d326583 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d326583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d326584 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d326584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d326585 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d326585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d326586 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d326586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d326587 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d326587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro105768 (p : Pattern) (ha : d14 p = 1) (hb : d326593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d326588 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105240 q ha hb
    | true =>
      simp only [d326588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105767 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d326589 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d326590 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d326591 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d326591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d326592 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d326592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d326593 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d326593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105769 (p : Pattern) (ha : d14 p = 1) (hb : d326599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d326594 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105768 q ha hb
    | true =>
      simp only [d326594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d326595 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d326596 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d326596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d326597 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d326597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d326598 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d326598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d326599 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d326599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105770 (p : Pattern) (ha : d14 p = 1) (hb : d326605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d326600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105267 q ha hb
    | true =>
      simp only [d326600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105769 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d326601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d326602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d326602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d326603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d326604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d326605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105771 (p : Pattern) (ha : d14 p = 1) (hb : d326611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46932 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105233 q ha hb
    | true =>
      simp only [d46932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105236 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46933 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105764 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d326606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105770 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d326607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d326607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d326608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d326608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d326609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d326609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d326610 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d326610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d326611 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d326611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105772 (p : Pattern) (ha : d14 p = 1) (hb : d326617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d326612 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105771 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d326613 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d326614 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d326615 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d326616 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d326617 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d326617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105773 (p : Pattern) (ha : d14 p = 1) (hb : d367603 p = 1) : d358777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d49 q = 1) : d49 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44916 q = 1) : d357633 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105280 q ha hb
    | true =>
      simp only [d44916, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44976 q = 1) : d357693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44976, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d44977 q = 1) : d357694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44977, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d44978 q = 1) : d357695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44978, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d44979 q = 1) : d357696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44979, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d367603 q = 1) : d358777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367603, d358777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367603, d358777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro105774 (p : Pattern) (ha : d14 p = 1) (hb : d367613 p = 1) : d358787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d83 q = 1) : d83 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44952 q = 1) : d357669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44952, d357669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105285 q ha hb
    | true =>
      simp only [d44952, d357669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367609 q = 1) : d358783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367609, d358783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367609, d358783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367610 q = 1) : d358784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367610, d358784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367610, d358784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367611 q = 1) : d358785 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367611, d358785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367611, d358785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367612 q = 1) : d358786 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367612, d358786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367612, d358786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d367613 q = 1) : d358787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367613, d358787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367613, d358787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro105775 (p : Pattern) (ha : d14 p = 1) (hb : d367619 p = 1) : d358793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d44981 q = 1) : d357698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d357698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105288 q ha hb
    | true =>
      simp only [d44981, d357698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105289 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44982 q = 1) : d357699 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d357699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44982, d357699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367601 q = 1) : d358775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367601, d358775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367601, d358775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367602 q = 1) : d358776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367602, d358776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367602, d358776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367604 q = 1) : d358778 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367604, d358778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367604, d358778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105773 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367605 q = 1) : d358779 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367605, d358779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367605, d358779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d367606 q = 1) : d358780 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367606, d358780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367606, d358780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d367607 q = 1) : d358781 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367607, d358781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367607, d358781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d367608 q = 1) : d358782 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367608, d358782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367608, d358782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d367614 q = 1) : d358788 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367614, d358788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367614, d358788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105774 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d367615 q = 1) : d358789 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367615, d358789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367615, d358789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d367616 q = 1) : d358790 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367616, d358790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367616, d358790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d367617 q = 1) : d358791 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367617, d358791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367617, d358791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d367618 q = 1) : d358792 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367618, d358792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367618, d358792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d367619 q = 1) : d358793 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367619, d358793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367619, d358793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105776 (p : Pattern) (ha : d14 p = 1) (hb : d367625 p = 1) : d358799 p = 1 := by
  have h0 (q : Pattern) (ha : d14 q = 1) (hb : d53652 q = 1) : d53652 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367620 q = 1) : d358794 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367620, d358794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367620, d358794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105775 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367621 q = 1) : d358795 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367621, d358795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367621, d358795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367622 q = 1) : d358796 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367622, d358796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367622, d358796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367623 q = 1) : d358797 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367623, d358797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367623, d358797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367624 q = 1) : d358798 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367624, d358798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367624, d358798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d367625 q = 1) : d358799 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367625, d358799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d367625, d358799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro105777 (p : Pattern) (ha : d14 p = 1) (hb : d367628 p = 1) : d358802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d45200 q = 1) : d357866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d357866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105319 q ha hb
    | true =>
      simp only [d45200, d357866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105320 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d45201 q = 1) : d357867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45201, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d45202 q = 1) : d357868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45202, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d45203 q = 1) : d357869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45203, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d45204 q = 1) : d357870 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45204, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367628 q = 1) : d358802 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367628, d358802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367628, d358802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105778 (p : Pattern) (ha : d14 p = 1) (hb : d367639 p = 1) : d358813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367634 q = 1) : d358808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367634, d358808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105356 q ha hb
    | true =>
      simp only [d367634, d358808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105326 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367635 q = 1) : d358809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367635, d358809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367635, d358809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367636 q = 1) : d358810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367636, d358810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367636, d358810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367637 q = 1) : d358811 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367637, d358811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367637, d358811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367638 q = 1) : d358812 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367638, d358812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367638, d358812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367639 q = 1) : d358813 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367639, d358813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367639, d358813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105779 (p : Pattern) (ha : d14 p = 1) (hb : d367645 p = 1) : d358819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d45206 q = 1) : d357872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45206, d357872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105318 q ha hb
    | true =>
      simp only [d45206, d357872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105321 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d45207 q = 1) : d357873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45207, d357873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45207, d357873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367626 q = 1) : d358800 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367626, d358800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367626, d358800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367627 q = 1) : d358801 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367627, d358801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367627, d358801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367629 q = 1) : d358803 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367629, d358803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367629, d358803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105777 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367630 q = 1) : d358804 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367630, d358804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367630, d358804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d367631 q = 1) : d358805 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367631, d358805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367631, d358805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d367632 q = 1) : d358806 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367632, d358806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367632, d358806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d367633 q = 1) : d358807 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367633, d358807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367633, d358807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d367640 q = 1) : d358814 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367640, d358814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367640, d358814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105778 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d367641 q = 1) : d358815 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367641, d358815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367641, d358815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d367642 q = 1) : d358816 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367642, d358816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367642, d358816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d367643 q = 1) : d358817 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367643, d358817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367643, d358817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d367644 q = 1) : d358818 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367644, d358818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367644, d358818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d367645 q = 1) : d358819 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367645, d358819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367645, d358819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105780 (p : Pattern) (ha : d14 p = 1) (hb : d367651 p = 1) : d358825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367646 q = 1) : d358820 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367646, d358820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367646, d358820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105779 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367647 q = 1) : d358821 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367647, d358821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367647, d358821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367648 q = 1) : d358822 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367648, d358822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367648, d358822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367649 q = 1) : d358823 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367649, d358823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367649, d358823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367650 q = 1) : d358824 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367650, d358824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367650, d358824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367651 q = 1) : d358825 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367651, d358825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367651, d358825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105781 (p : Pattern) (ha : d14 p = 1) (hb : d367655 p = 1) : d358829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d45542 q = 1) : d358126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45542, d358126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105370 q ha hb
    | true =>
      simp only [d45542, d358126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105371 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d45543 q = 1) : d358127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45543, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45543, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d45544 q = 1) : d358128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45544, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45544, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d45545 q = 1) : d358129 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45545, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45545, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d45546 q = 1) : d358130 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45546, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45546, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367655 q = 1) : d358829 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367655, d358829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367655, d358829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105782 (p : Pattern) (ha : d14 p = 1) (hb : d367666 p = 1) : d358840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367661 q = 1) : d358835 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367661, d358835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105410 q ha hb
    | true =>
      simp only [d367661, d358835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105379 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367662 q = 1) : d358836 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367662, d358836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367662, d358836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367663 q = 1) : d358837 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367663, d358837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367663, d358837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367664 q = 1) : d358838 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367664, d358838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367664, d358838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367665 q = 1) : d358839 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367665, d358839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367665, d358839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367666 q = 1) : d358840 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367666, d358840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367666, d358840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105783 (p : Pattern) (ha : d14 p = 1) (hb : d367672 p = 1) : d358846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d45548 q = 1) : d358132 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45548, d358132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105369 q ha hb
    | true =>
      simp only [d45548, d358132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105372 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d45549 q = 1) : d358133 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d45549, d358133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45549, d358133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367653 q = 1) : d358827 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367653, d358827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367653, d358827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367654 q = 1) : d358828 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367654, d358828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367654, d358828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367656 q = 1) : d358830 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367656, d358830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367656, d358830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105781 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367657 q = 1) : d358831 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367657, d358831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367657, d358831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d367658 q = 1) : d358832 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367658, d358832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367658, d358832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d367659 q = 1) : d358833 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367659, d358833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367659, d358833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d367660 q = 1) : d358834 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367660, d358834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367660, d358834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d367667 q = 1) : d358841 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367667, d358841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367667, d358841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105782 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d367668 q = 1) : d358842 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367668, d358842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367668, d358842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d367669 q = 1) : d358843 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367669, d358843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367669, d358843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d367670 q = 1) : d358844 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367670, d358844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367670, d358844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d367671 q = 1) : d358845 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367671, d358845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367671, d358845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d367672 q = 1) : d358846 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367672, d358846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367672, d358846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105784 (p : Pattern) (ha : d14 p = 1) (hb : d367678 p = 1) : d358852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367673 q = 1) : d358847 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367673, d358847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367673, d358847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105783 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367674 q = 1) : d358848 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367674, d358848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367674, d358848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367675 q = 1) : d358849 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367675, d358849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367675, d358849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367676 q = 1) : d358850 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367676, d358850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367676, d358850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367677 q = 1) : d358851 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367677, d358851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367677, d358851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367678 q = 1) : d358852 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367678, d358852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367678, d358852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105785 (p : Pattern) (ha : d14 p = 1) (hb : d367683 p = 1) : d358857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46006 q = 1) : d358463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46006, d358463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105429 q ha hb
    | true =>
      simp only [d46006, d358463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105430 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46007 q = 1) : d358464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46007, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46007, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d46008 q = 1) : d358465 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46008, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46008, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d46009 q = 1) : d358466 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46009, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46009, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d46010 q = 1) : d358467 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46010, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46010, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367683 q = 1) : d358857 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367683, d358857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367683, d358857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105786 (p : Pattern) (ha : d14 p = 1) (hb : d367694 p = 1) : d358868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367689 q = 1) : d358863 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d367689, d358863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105469 q ha hb
    | true =>
      simp only [d367689, d358863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105438 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367690 q = 1) : d358864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d367690, d358864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367690, d358864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367691 q = 1) : d358865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d367691, d358865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367691, d358865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367692 q = 1) : d358866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d367692, d358866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367692, d358866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367693 q = 1) : d358867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d367693, d358867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367693, d358867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367694 q = 1) : d358868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d367694, d358868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367694, d358868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105787 (p : Pattern) (ha : d14 p = 1) (hb : d367700 p = 1) : d358874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d46012 q = 1) : d358469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46012, d358469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105428 q ha hb
    | true =>
      simp only [d46012, d358469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105431 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d46013 q = 1) : d358470 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46013, d358470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46013, d358470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367681 q = 1) : d358855 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367681, d358855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367681, d358855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367682 q = 1) : d358856 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367682, d358856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367682, d358856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367684 q = 1) : d358858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367684, d358858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367684, d358858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105785 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367685 q = 1) : d358859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367685, d358859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367685, d358859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d367686 q = 1) : d358860 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367686, d358860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367686, d358860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d367687 q = 1) : d358861 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367687, d358861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d367687, d358861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d367688 q = 1) : d358862 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367688, d358862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367688, d358862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d367695 q = 1) : d358869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d367695, d358869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367695, d358869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105786 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d367696 q = 1) : d358870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d367696, d358870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d367696, d358870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d367697 q = 1) : d358871 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d367697, d358871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d367697, d358871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d367698 q = 1) : d358872 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d367698, d358872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d367698, d358872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d367699 q = 1) : d358873 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d367699, d358873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367699, d358873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d367700 q = 1) : d358874 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d367700, d358874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d367700, d358874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105788 (p : Pattern) (ha : d14 p = 1) (hb : d367706 p = 1) : d358880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367701 q = 1) : d358875 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d367701, d358875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367701, d358875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105787 q ha hb
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367702 q = 1) : d358876 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d367702, d358876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367702, d358876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367703 q = 1) : d358877 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d367703, d358877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367703, d358877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367704 q = 1) : d358878 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d367704, d358878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367704, d358878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367705 q = 1) : d358879 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d367705, d358879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367705, d358879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367706 q = 1) : d358880 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d367706, d358880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367706, d358880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105789 (p : Pattern) (ha : d14 p = 1) (hb : d367712 p = 1) : d358886 p = 1 := by
  have h0 (q : Pattern) (ha : d14 q = 1) (hb : d367652 q = 1) : d358826 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367652, d358826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105776 q ha hb
    | true =>
      simp only [d367652, d358826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105780 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367679 q = 1) : d358853 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367679, d358853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367679, d358853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105784 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367680 q = 1) : d358854 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367680, d358854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d367680, d358854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367707 q = 1) : d358881 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d367707, d358881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367707, d358881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105788 q ha hb
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367708 q = 1) : d358882 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d367708, d358882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d367708, d358882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367709 q = 1) : d358883 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d367709, d358883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367709, d358883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d321906 q = 1) : d321906 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d367710 q = 1) : d358884 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d367710, d358884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367710, d358884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d326618 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105772 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d326619 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d326620 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d326621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14 q = 1) (hb : d367711 q = 1) : d358885 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d367711, d358885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d367711, d358885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14 q = 1) (hb : d367712 q = 1) : d358886 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d367712, d358886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d367712, d358886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h14 p ha hb
theorem andIntro105790 (p : Pattern) (ha : d14 p = 1) (hb : d367718 p = 1) : d358892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367713 q = 1) : d358887 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d367713, d358887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105789 q ha hb
    | true =>
      simp only [d367713, d358887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367714 q = 1) : d358888 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d367714, d358888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367714, d358888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367715 q = 1) : d358889 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d367715, d358889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367715, d358889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367716 q = 1) : d358890 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d367716, d358890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367716, d358890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367717 q = 1) : d358891 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d367717, d358891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367717, d358891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367718 q = 1) : d358892 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d367718, d358892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367718, d358892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105791 (p : Pattern) (ha : d14 p = 1) (hb : d367724 p = 1) : d358898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367719 q = 1) : d358893 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d367719, d358893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105790 q ha hb
    | true =>
      simp only [d367719, d358893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367720 q = 1) : d358894 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d367720, d358894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367720, d358894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367721 q = 1) : d358895 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d367721, d358895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367721, d358895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367722 q = 1) : d358896 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, d358896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367722, d358896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367723 q = 1) : d358897 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d358897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367723, d358897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367724 q = 1) : d358898 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, d358898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367724, d358898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105792 (p : Pattern) (ha : d14 p = 1) (hb : d367730 p = 1) : d358904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367725 q = 1) : d358899 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, d358899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105791 q ha hb
    | true =>
      simp only [d367725, d358899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367726 q = 1) : d358900 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, d358900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, d358900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367727 q = 1) : d358901 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, d358901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, d358901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367728 q = 1) : d358902 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, d358902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, d358902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367729 q = 1) : d358903 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, d358903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, d358903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367730 q = 1) : d358904 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, d358904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, d358904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105793 (p : Pattern) (ha : d14 p = 1) (hb : d367736 p = 1) : d358910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367731 q = 1) : d358905 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, d358905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105792 q ha hb
    | true =>
      simp only [d367731, d358905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367732 q = 1) : d358906 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, d358906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, d358906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367733 q = 1) : d358907 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, d358907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, d358907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367734 q = 1) : d358908 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, d358908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, d358908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367735 q = 1) : d358909 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, d358909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, d358909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367736 q = 1) : d358910 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, d358910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, d358910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105794 (p : Pattern) (ha : d14 p = 1) (hb : d367742 p = 1) : d358916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367737 q = 1) : d358911 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, d358911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105793 q ha hb
    | true =>
      simp only [d367737, d358911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367738 q = 1) : d358912 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, d358912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, d358912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367739 q = 1) : d358913 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, d358913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, d358913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367740 q = 1) : d358914 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, d358914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, d358914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367741 q = 1) : d358915 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, d358915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, d358915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367742 q = 1) : d358916 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, d358916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, d358916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105795 (p : Pattern) (ha : d14 p = 1) (hb : d367748 p = 1) : d358922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367743 q = 1) : d358917 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, d358917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105794 q ha hb
    | true =>
      simp only [d367743, d358917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367744 q = 1) : d358918 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, d358918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, d358918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367745 q = 1) : d358919 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, d358919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, d358919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367746 q = 1) : d358920 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, d358920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, d358920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367747 q = 1) : d358921 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, d358921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, d358921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367748 q = 1) : d358922 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, d358922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, d358922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105796 (p : Pattern) (ha : d14 p = 1) (hb : d367754 p = 1) : d358928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14 q = 1) (hb : d367749 q = 1) : d358923 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, d358923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105795 q ha hb
    | true =>
      simp only [d367749, d358923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d367750 q = 1) : d358924 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, d358924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, d358924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d367751 q = 1) : d358925 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, d358925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, d358925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d367752 q = 1) : d358926 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, d358926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, d358926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d14 q = 1) (hb : d367753 q = 1) : d358927 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, d358927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, d358927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d14 q = 1) (hb : d367754 q = 1) : d358928 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, d358928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, d358928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105797 (p : Pattern) (ha : d306197 p = 1) (hb : d357690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306186 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306064 q = 1) (hb : d357626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306064, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105488 q ha hb
    | true =>
      simp only [d306064, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d306187 q = 1) (hb : d357686 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306187, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306187, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306193 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306194 q = 1) (hb : d357687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306194, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306194, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306195 q = 1) (hb : d357688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306195, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306195, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306196 q = 1) (hb : d357689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306196, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306196, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306197 q = 1) (hb : d357690 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306197, d357690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306197, d357690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105798 (p : Pattern) (ha : d306216 p = 1) (hb : d357697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306144 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306150 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306064 q = 1) (hb : d357626 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306064, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105488 q ha hb
    | true =>
      simp only [d306064, d357626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d306187 q = 1) (hb : d357686 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306187, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306187, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306193 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306194 q = 1) (hb : d357687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306194, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306194, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306195 q = 1) (hb : d357688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306195, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306195, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306196 q = 1) (hb : d357689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306196, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306196, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306202 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306206 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306208 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306071 q = 1) (hb : d357633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306071, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105490 q ha hb
    | true =>
      simp only [d306071, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d306209 q = 1) (hb : d357693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306209, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306209, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306212 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306213 q = 1) (hb : d357694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306213, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306213, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306214 q = 1) (hb : d357695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306214, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306214, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306215 q = 1) (hb : d357696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306215, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306215, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306216 q = 1) (hb : d357697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306216, d357697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306216, d357697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105799 (p : Pattern) (ha : d306225 p = 1) (hb : d358777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306208 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306071 q = 1) (hb : d357633 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306071, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105490 q ha hb
    | true =>
      simp only [d306071, d357633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d306209 q = 1) (hb : d357693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306209, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306209, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306212 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306213 q = 1) (hb : d357694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306213, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306213, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306223 q = 1) (hb : d357695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306223, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306223, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306224 q = 1) (hb : d357696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306224, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306224, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306225 q = 1) (hb : d358777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306225, d358777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306225, d358777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105800 (p : Pattern) (ha : d306265 p = 1) (hb : d358787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306107 q = 1) (hb : d357669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306107, d357669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105495 q ha hb
    | true =>
      simp only [d306107, d357669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d306255 q = 1) (hb : d358783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306255, d358783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306255, d358783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306261 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306262 q = 1) (hb : d358784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306262, d358784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306262, d358784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306263 q = 1) (hb : d358785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306263, d358785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306263, d358785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306264 q = 1) (hb : d358786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306264, d358786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306264, d358786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306265 q = 1) (hb : d358787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306265, d358787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306265, d358787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105801 (p : Pattern) (ha : d306271 p = 1) (hb : d358793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306138 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306217 q = 1) (hb : d357698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306217, d357698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105797 q ha hb
    | true =>
      simp only [d306217, d357698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105798 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306219 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306220 q = 1) (hb : d357699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306220, d357699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306220, d357699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306221 q = 1) (hb : d358775 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306221, d358775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306221, d358775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306222 q = 1) (hb : d358776 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306222, d358776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306222, d358776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306226 q = 1) (hb : d358778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306226, d358778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306226, d358778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105799 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306227 q = 1) (hb : d358779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306227, d358779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306227, d358779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306228 q = 1) (hb : d358780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306228, d358780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306228, d358780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306229 q = 1) (hb : d358781 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306229, d358781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306229, d358781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306230 q = 1) (hb : d358782 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306230, d358782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306230, d358782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306266 q = 1) (hb : d358788 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306266, d358788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306266, d358788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105800 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306267 q = 1) (hb : d358789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306267, d358789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306267, d358789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306268 q = 1) (hb : d358790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306268, d358790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306268, d358790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306269 q = 1) (hb : d358791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306269, d358791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306269, d358791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306270 q = 1) (hb : d358792 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306270, d358792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306270, d358792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306271 q = 1) (hb : d358793 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306271, d358793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306271, d358793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105802 (p : Pattern) (ha : d306277 p = 1) (hb : d358799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d306119 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d306119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d306119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80480 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d306120 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d306120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d306120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d306121 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d306121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d306121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d306122 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d306122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d306122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d306123 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d306123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d306123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306272 q = 1) (hb : d358794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306272, d358794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306272, d358794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105801 q ha hb
  have h8 (q : Pattern) (ha : d306273 q = 1) (hb : d358795 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306273, d358795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306273, d358795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306274 q = 1) (hb : d358796 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306274, d358796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306274, d358796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306275 q = 1) (hb : d358797 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306275, d358797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306275, d358797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d306276 q = 1) (hb : d358798 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306276, d358798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306276, d358798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d306277 q = 1) (hb : d358799 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306277, d358799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d306277, d358799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro105803 (p : Pattern) (ha : d306394 p = 1) (hb : d357861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306383 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306295 q = 1) (hb : d357856 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306295, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105526 q ha hb
    | true =>
      simp only [d306295, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105527 q ha hb
  have h5 (q : Pattern) (ha : d306384 q = 1) (hb : d357857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306384, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306384, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306390 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306391 q = 1) (hb : d357858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306391, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306391, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306392 q = 1) (hb : d357859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306392, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306392, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306393 q = 1) (hb : d357860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306393, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306393, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306394 q = 1) (hb : d357861 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306394, d357861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306394, d357861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105804 (p : Pattern) (ha : d306415 p = 1) (hb : d357871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306321 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306330 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306295 q = 1) (hb : d357856 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306295, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105526 q ha hb
    | true =>
      simp only [d306295, d357856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105527 q ha hb
  have h4 (q : Pattern) (ha : d306384 q = 1) (hb : d357857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306384, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306384, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306390 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306391 q = 1) (hb : d357858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306391, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306391, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306392 q = 1) (hb : d357859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306392, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306392, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306393 q = 1) (hb : d357860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306393, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306393, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306400 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306405 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306407 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306305 q = 1) (hb : d357866 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306305, d357866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105529 q ha hb
    | true =>
      simp only [d306305, d357866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105530 q ha hb
  have h13 (q : Pattern) (ha : d306408 q = 1) (hb : d357867 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306408, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306408, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306411 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306412 q = 1) (hb : d357868 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306412, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306412, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306413 q = 1) (hb : d357869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306413, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306413, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306414 q = 1) (hb : d357870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306414, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306414, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306415 q = 1) (hb : d357871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306415, d357871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306415, d357871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105805 (p : Pattern) (ha : d306435 p = 1) (hb : d358802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306407 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306305 q = 1) (hb : d357866 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306305, d357866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105529 q ha hb
    | true =>
      simp only [d306305, d357866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105530 q ha hb
  have h3 (q : Pattern) (ha : d306408 q = 1) (hb : d357867 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306408, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306408, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306411 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306412 q = 1) (hb : d357868 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306412, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306412, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306433 q = 1) (hb : d357869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306433, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306433, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306434 q = 1) (hb : d357870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306434, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306434, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306435 q = 1) (hb : d358802 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306435, d358802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306435, d358802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105806 (p : Pattern) (ha : d306503 p = 1) (hb : d358813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306492 q = 1) (hb : d358808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306492, d358808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105564 q ha hb
    | true =>
      simp only [d306492, d358808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105567 q ha hb
  have h3 (q : Pattern) (ha : d306493 q = 1) (hb : d358809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306493, d358809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306493, d358809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306499 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306500 q = 1) (hb : d358810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306500, d358810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306500, d358810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306501 q = 1) (hb : d358811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306501, d358811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306501, d358811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306502 q = 1) (hb : d358812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306502, d358812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306502, d358812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306503 q = 1) (hb : d358813 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306503, d358813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306503, d358813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105807 (p : Pattern) (ha : d306516 p = 1) (hb : d358819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306416 q = 1) (hb : d357872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306416, d357872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105803 q ha hb
    | true =>
      simp only [d306416, d357872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105804 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306430 q = 1) (hb : d357873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306430, d357873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306430, d357873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306431 q = 1) (hb : d358800 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306431, d358800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306431, d358800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306432 q = 1) (hb : d358801 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306432, d358801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306432, d358801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306436 q = 1) (hb : d358803 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306436, d358803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306436, d358803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105805 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d306438 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306439 q = 1) (hb : d358804 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306439, d358804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306439, d358804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306440 q = 1) (hb : d358805 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306440, d358805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306440, d358805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306441 q = 1) (hb : d358806 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306441, d358806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306441, d358806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306442 q = 1) (hb : d358807 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306442, d358807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306442, d358807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306504 q = 1) (hb : d358814 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306504, d358814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306504, d358814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105806 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306511 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306512 q = 1) (hb : d358815 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306512, d358815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306512, d358815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306513 q = 1) (hb : d358816 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306513, d358816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306513, d358816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306514 q = 1) (hb : d358817 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306514, d358817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306514, d358817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306515 q = 1) (hb : d358818 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306515, d358818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306515, d358818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306516 q = 1) (hb : d358819 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306516, d358819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306516, d358819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105808 (p : Pattern) (ha : d306522 p = 1) (hb : d358825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306517 q = 1) (hb : d358820 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306517, d358820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306517, d358820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105807 q ha hb
  have h2 (q : Pattern) (ha : d306518 q = 1) (hb : d358821 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306518, d358821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306518, d358821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306519 q = 1) (hb : d358822 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306519, d358822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306519, d358822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306520 q = 1) (hb : d358823 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306520, d358823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306520, d358823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306521 q = 1) (hb : d358824 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306521, d358824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306521, d358824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306522 q = 1) (hb : d358825 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306522, d358825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306522, d358825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105809 (p : Pattern) (ha : d306670 p = 1) (hb : d358121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306585 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306594 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d306659 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306559 q = 1) (hb : d358116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306559, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105577 q ha hb
    | true =>
      simp only [d306559, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105578 q ha hb
  have h5 (q : Pattern) (ha : d306660 q = 1) (hb : d358117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306660, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d306660, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d306666 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d306667 q = 1) (hb : d358118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306667, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d306667, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d306668 q = 1) (hb : d358119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306668, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306668, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306669 q = 1) (hb : d358120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306669, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306669, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d306670 q = 1) (hb : d358121 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306670, d358121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306670, d358121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105810 (p : Pattern) (ha : d306691 p = 1) (hb : d358131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306585 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306559 q = 1) (hb : d358116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306559, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105577 q ha hb
    | true =>
      simp only [d306559, d358116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105578 q ha hb
  have h4 (q : Pattern) (ha : d306660 q = 1) (hb : d358117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306660, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d306660, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d306666 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306667 q = 1) (hb : d358118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306667, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306667, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d306668 q = 1) (hb : d358119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306668, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306668, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306669 q = 1) (hb : d358120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306669, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306669, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d306676 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d306681 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d306683 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306569 q = 1) (hb : d358126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306569, d358126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105580 q ha hb
    | true =>
      simp only [d306569, d358126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105581 q ha hb
  have h13 (q : Pattern) (ha : d306684 q = 1) (hb : d358127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306684, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d306684, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306687 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306688 q = 1) (hb : d358128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306688, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306688, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306689 q = 1) (hb : d358129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306689, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d306689, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d306690 q = 1) (hb : d358130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306690, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d306690, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d306691 q = 1) (hb : d358131 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306691, d358131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306691, d358131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105811 (p : Pattern) (ha : d306711 p = 1) (hb : d358829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306683 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306569 q = 1) (hb : d358126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306569, d358126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105580 q ha hb
    | true =>
      simp only [d306569, d358126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105581 q ha hb
  have h3 (q : Pattern) (ha : d306684 q = 1) (hb : d358127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306684, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306684, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306687 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306688 q = 1) (hb : d358128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306688, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306688, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306709 q = 1) (hb : d358129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306709, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306709, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306710 q = 1) (hb : d358130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306710, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306710, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306711 q = 1) (hb : d358829 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306711, d358829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306711, d358829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105812 (p : Pattern) (ha : d306796 p = 1) (hb : d358840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306785 q = 1) (hb : d358835 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306785, d358835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105619 q ha hb
    | true =>
      simp only [d306785, d358835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105622 q ha hb
  have h3 (q : Pattern) (ha : d306786 q = 1) (hb : d358836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d306786, d358836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306786, d358836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d306792 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306793 q = 1) (hb : d358837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306793, d358837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306793, d358837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306794 q = 1) (hb : d358838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d306794, d358838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306794, d358838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306795 q = 1) (hb : d358839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d306795, d358839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306795, d358839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d306796 q = 1) (hb : d358840 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d306796, d358840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306796, d358840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105813 (p : Pattern) (ha : d306809 p = 1) (hb : d358846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306692 q = 1) (hb : d358132 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306692, d358132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105809 q ha hb
    | true =>
      simp only [d306692, d358132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105810 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306706 q = 1) (hb : d358133 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306706, d358133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d306706, d358133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d306707 q = 1) (hb : d358827 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306707, d358827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306707, d358827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d306708 q = 1) (hb : d358828 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306708, d358828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306708, d358828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306712 q = 1) (hb : d358830 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306712, d358830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306712, d358830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105811 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d306714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d306715 q = 1) (hb : d358831 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306715, d358831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d306715, d358831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d306716 q = 1) (hb : d358832 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306716, d358832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d306716, d358832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d306717 q = 1) (hb : d358833 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306717, d358833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306717, d358833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d306718 q = 1) (hb : d358834 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306718, d358834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306718, d358834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d306797 q = 1) (hb : d358841 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d306797, d358841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d306797, d358841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105812 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d306804 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d306805 q = 1) (hb : d358842 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d306805, d358842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d306805, d358842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d306806 q = 1) (hb : d358843 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d306806, d358843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d306806, d358843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d306807 q = 1) (hb : d358844 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d306807, d358844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d306807, d358844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d306808 q = 1) (hb : d358845 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d306808, d358845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d306808, d358845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d306809 q = 1) (hb : d358846 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d306809, d358846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d306809, d358846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105814 (p : Pattern) (ha : d306815 p = 1) (hb : d358852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306810 q = 1) (hb : d358847 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d306810, d358847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306810, d358847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105813 q ha hb
  have h2 (q : Pattern) (ha : d306811 q = 1) (hb : d358848 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d306811, d358848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306811, d358848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d306812 q = 1) (hb : d358849 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d306812, d358849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306812, d358849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306813 q = 1) (hb : d358850 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d306813, d358850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306813, d358850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306814 q = 1) (hb : d358851 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d306814, d358851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306814, d358851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d306815 q = 1) (hb : d358852 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d306815, d358852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d306815, d358852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105815 (p : Pattern) (ha : d307028 p = 1) (hb : d358458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d306909 q = 1) (hb : d358453 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d358453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105637 q ha hb
    | true =>
      simp only [d306909, d358453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105638 q ha hb
  have h5 (q : Pattern) (ha : d307009 q = 1) (hb : d358454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d358454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307009, d358454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307025 q = 1) (hb : d358455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d358455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307025, d358455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307026 q = 1) (hb : d358456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d358456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307026, d358456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307027 q = 1) (hb : d358457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d358457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307027, d358457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307028 q = 1) (hb : d358458 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307028, d358458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307028, d358458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105816 (p : Pattern) (ha : d307049 p = 1) (hb : d358468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306909 q = 1) (hb : d358453 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d358453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105637 q ha hb
    | true =>
      simp only [d306909, d358453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105638 q ha hb
  have h4 (q : Pattern) (ha : d307009 q = 1) (hb : d358454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d358454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307009, d358454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307025 q = 1) (hb : d358455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d358455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307025, d358455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307026 q = 1) (hb : d358456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d358456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307026, d358456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307027 q = 1) (hb : d358457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d358457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307027, d358457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307034 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307039 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306919 q = 1) (hb : d358463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d358463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105640 q ha hb
    | true =>
      simp only [d306919, d358463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105641 q ha hb
  have h13 (q : Pattern) (ha : d307042 q = 1) (hb : d358464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307042, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307046 q = 1) (hb : d358465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307046, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307047 q = 1) (hb : d358466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307047, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307047, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307048 q = 1) (hb : d358467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307048, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307048, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307049 q = 1) (hb : d358468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307049, d358468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307049, d358468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105817 (p : Pattern) (ha : d307069 p = 1) (hb : d358857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306919 q = 1) (hb : d358463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d358463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105640 q ha hb
    | true =>
      simp only [d306919, d358463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105641 q ha hb
  have h3 (q : Pattern) (ha : d307042 q = 1) (hb : d358464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307042, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307046 q = 1) (hb : d358465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307046, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307067 q = 1) (hb : d358466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307067, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307067, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307068 q = 1) (hb : d358467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307068, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307068, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307069 q = 1) (hb : d358857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307069, d358857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307069, d358857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105818 (p : Pattern) (ha : d307190 p = 1) (hb : d358868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307170 q = 1) (hb : d358863 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307170, d358863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105681 q ha hb
    | true =>
      simp only [d307170, d358863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105686 q ha hb
  have h3 (q : Pattern) (ha : d307171 q = 1) (hb : d358864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307171, d358864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307171, d358864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307186 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307187 q = 1) (hb : d358865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307187, d358865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307187, d358865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307188 q = 1) (hb : d358866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307188, d358866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307188, d358866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307189 q = 1) (hb : d358867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307189, d358867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307189, d358867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307190 q = 1) (hb : d358868 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307190, d358868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307190, d358868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105819 (p : Pattern) (ha : d307203 p = 1) (hb : d358874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306927 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307050 q = 1) (hb : d358469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307050, d358469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105815 q ha hb
    | true =>
      simp only [d307050, d358469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105816 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307064 q = 1) (hb : d358470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307064, d358470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307064, d358470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307065 q = 1) (hb : d358855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307065, d358855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307065, d358855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307066 q = 1) (hb : d358856 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307066, d358856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307066, d358856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307070 q = 1) (hb : d358858 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307070, d358858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307070, d358858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105817 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307073 q = 1) (hb : d358859 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307073, d358859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307073, d358859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307074 q = 1) (hb : d358860 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307074, d358860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307074, d358860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307075 q = 1) (hb : d358861 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307075, d358861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307075, d358861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307076 q = 1) (hb : d358862 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307076, d358862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307076, d358862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307191 q = 1) (hb : d358869 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307191, d358869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307191, d358869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105818 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307199 q = 1) (hb : d358870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307199, d358870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307199, d358870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307200 q = 1) (hb : d358871 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307200, d358871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307200, d358871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307201 q = 1) (hb : d358872 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307201, d358872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307201, d358872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307202 q = 1) (hb : d358873 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307202, d358873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307202, d358873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307203 q = 1) (hb : d358874 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307203, d358874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307203, d358874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105820 (p : Pattern) (ha : d307209 p = 1) (hb : d358880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307204 q = 1) (hb : d358875 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307204, d358875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307204, d358875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105819 q ha hb
  have h2 (q : Pattern) (ha : d307205 q = 1) (hb : d358876 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307205, d358876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307205, d358876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307206 q = 1) (hb : d358877 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307206, d358877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307206, d358877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307207 q = 1) (hb : d358878 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307207, d358878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307207, d358878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307208 q = 1) (hb : d358879 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307208, d358879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307208, d358879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307209 q = 1) (hb : d358880 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307209, d358880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307209, d358880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105821 (p : Pattern) (ha : d46527 p = 1) (hb : d307443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46522 q = 1) (hb : d307324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d307324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105704 q ha hb
    | true =>
      simp only [d46522, d307324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105705 q ha hb
  have h5 (q : Pattern) (ha : d46523 q = 1) (hb : d307411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d307411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46523, d307411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46524 q = 1) (hb : d307440 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d307440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46524, d307440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46525 q = 1) (hb : d307441 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d307441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46525, d307441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46526 q = 1) (hb : d307442 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d307442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46526, d307442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46527 q = 1) (hb : d307443 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, d307443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46527, d307443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105822 (p : Pattern) (ha : d46537 p = 1) (hb : d307464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46522 q = 1) (hb : d307324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d307324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105704 q ha hb
    | true =>
      simp only [d46522, d307324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105705 q ha hb
  have h4 (q : Pattern) (ha : d46523 q = 1) (hb : d307411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d307411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46523, d307411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46524 q = 1) (hb : d307440 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d307440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46524, d307440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46525 q = 1) (hb : d307441 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d307441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46525, d307441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46526 q = 1) (hb : d307442 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d307442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d307442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307449 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307454 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d46532 q = 1) (hb : d307334 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d307334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105707 q ha hb
    | true =>
      simp only [d46532, d307334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105708 q ha hb
  have h13 (q : Pattern) (ha : d46533 q = 1) (hb : d307457 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d307457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46533, d307457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46534 q = 1) (hb : d307461 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d307461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46534, d307461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46535 q = 1) (hb : d307462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d307462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46535, d307462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46536 q = 1) (hb : d307463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d307463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46536, d307463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46537 q = 1) (hb : d307464 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, d307464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46537, d307464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105823 (p : Pattern) (ha : d307484 p = 1) (hb : d321880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46532 q = 1) (hb : d307334 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d307334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105707 q ha hb
    | true =>
      simp only [d46532, d307334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105708 q ha hb
  have h3 (q : Pattern) (ha : d46533 q = 1) (hb : d307457 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d307457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46533, d307457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46534 q = 1) (hb : d307461 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d307461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46534, d307461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46535 q = 1) (hb : d307482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d307482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d307482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46536 q = 1) (hb : d307483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d307483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d307483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307484 q = 1) (hb : d321880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307484, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307484, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105824 (p : Pattern) (ha : d307616 p = 1) (hb : d321891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307585 q = 1) (hb : d321886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307585, d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105748 q hb ha
    | true =>
      simp only [d307585, d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105716 q hb ha
  have h3 (q : Pattern) (ha : d307586 q = 1) (hb : d321887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307586, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307586, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307613 q = 1) (hb : d321888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307613, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307613, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307614 q = 1) (hb : d321889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307614, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307614, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307615 q = 1) (hb : d321890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307615, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307615, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307616 q = 1) (hb : d321891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307616, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307616, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105825 (p : Pattern) (ha : d307629 p = 1) (hb : d321897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d307465 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d307465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105821 q ha hb
    | true =>
      simp only [d46538, d307465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105822 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46539 q = 1) (hb : d307479 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d307479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, d307479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307480 q = 1) (hb : d321878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307480, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307480, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307481 q = 1) (hb : d321879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307481, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307481, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307485 q = 1) (hb : d321881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307485, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307485, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105823 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307487 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307488 q = 1) (hb : d321882 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307488, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307488, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307489 q = 1) (hb : d321883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307489, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307489, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307490 q = 1) (hb : d321884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307490, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307490, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307491 q = 1) (hb : d321885 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307491, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307491, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307617 q = 1) (hb : d321892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307617, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307617, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105824 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307625 q = 1) (hb : d321893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307625, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307625, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307626 q = 1) (hb : d321894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307626, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307626, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307627 q = 1) (hb : d321895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307627, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307627, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307628 q = 1) (hb : d321896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307628, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307628, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307629 q = 1) (hb : d321897 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307629, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307629, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105826 (p : Pattern) (ha : d307635 p = 1) (hb : d321903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307630 q = 1) (hb : d321898 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307630, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307630, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105825 q ha hb
  have h2 (q : Pattern) (ha : d307631 q = 1) (hb : d321899 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307631, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307631, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307632 q = 1) (hb : d321900 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307632, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307632, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307633 q = 1) (hb : d321901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307633, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307633, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307634 q = 1) (hb : d321902 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307634, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307634, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307635 q = 1) (hb : d321903 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307635, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307635, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105827 (p : Pattern) (ha : d307931 p = 1) (hb : d358886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d306523 q = 1) (hb : d358826 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306523, d358826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105802 q ha hb
    | true =>
      simp only [d306523, d358826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105808 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306816 q = 1) (hb : d358853 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306816, d358853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306816, d358853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105814 q ha hb
  have h3 (q : Pattern) (ha : d306817 q = 1) (hb : d358854 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d306817, d358854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d306817, d358854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307210 q = 1) (hb : d358881 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307210, d358881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307210, d358881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105820 q ha hb
  have h5 (q : Pattern) (ha : d307211 q = 1) (hb : d358882 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307211, d358882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307211, d358882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307212 q = 1) (hb : d358883 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307212, d358883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307212, d358883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307636 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307636, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307636, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105826 q ha hb
  have h8 (q : Pattern) (ha : d307637 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307637, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307637, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307638 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307638, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307638, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307639 q = 1) (hb : d358884 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307639, d358884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307639, d358884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307929 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d307930 q = 1) (hb : d358885 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d307930, d358885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307930, d358885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d307931 q = 1) (hb : d358886 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d307931, d358886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307931, d358886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h13 p ha hb
theorem andIntro105828 (p : Pattern) (ha : d307937 p = 1) (hb : d358892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307932 q = 1) (hb : d358887 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d307932, d358887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105827 q ha hb
    | true =>
      simp only [d307932, d358887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307933 q = 1) (hb : d358888 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d307933, d358888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307933, d358888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307934 q = 1) (hb : d358889 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d307934, d358889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307934, d358889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307935 q = 1) (hb : d358890 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d307935, d358890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307935, d358890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307936 q = 1) (hb : d358891 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d307936, d358891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307936, d358891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307937 q = 1) (hb : d358892 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d307937, d358892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307937, d358892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105829 (p : Pattern) (ha : d307943 p = 1) (hb : d358898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307938 q = 1) (hb : d358893 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d307938, d358893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105828 q ha hb
    | true =>
      simp only [d307938, d358893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307939 q = 1) (hb : d358894 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d307939, d358894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307939, d358894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307940 q = 1) (hb : d358895 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d307940, d358895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307940, d358895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307941 q = 1) (hb : d358896 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d307941, d358896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307941, d358896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307942 q = 1) (hb : d358897 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d307942, d358897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307942, d358897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307943 q = 1) (hb : d358898 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d307943, d358898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307943, d358898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105830 (p : Pattern) (ha : d307949 p = 1) (hb : d358904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307944 q = 1) (hb : d358899 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d307944, d358899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105829 q ha hb
    | true =>
      simp only [d307944, d358899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307945 q = 1) (hb : d358900 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d307945, d358900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307945, d358900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307946 q = 1) (hb : d358901 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d307946, d358901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307946, d358901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307947 q = 1) (hb : d358902 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d307947, d358902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307947, d358902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307948 q = 1) (hb : d358903 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d307948, d358903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307948, d358903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307949 q = 1) (hb : d358904 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d307949, d358904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307949, d358904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105831 (p : Pattern) (ha : d307955 p = 1) (hb : d358910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307950 q = 1) (hb : d358905 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d307950, d358905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105830 q ha hb
    | true =>
      simp only [d307950, d358905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307951 q = 1) (hb : d358906 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d307951, d358906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307951, d358906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307952 q = 1) (hb : d358907 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d307952, d358907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307952, d358907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307953 q = 1) (hb : d358908 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d307953, d358908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307953, d358908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307954 q = 1) (hb : d358909 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d307954, d358909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307954, d358909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307955 q = 1) (hb : d358910 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d307955, d358910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307955, d358910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105832 (p : Pattern) (ha : d307961 p = 1) (hb : d358916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307956 q = 1) (hb : d358911 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d307956, d358911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105831 q ha hb
    | true =>
      simp only [d307956, d358911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307957 q = 1) (hb : d358912 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d307957, d358912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307957, d358912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307958 q = 1) (hb : d358913 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d307958, d358913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307958, d358913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307959 q = 1) (hb : d358914 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d307959, d358914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307959, d358914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307960 q = 1) (hb : d358915 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d307960, d358915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307960, d358915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307961 q = 1) (hb : d358916 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d307961, d358916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307961, d358916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105833 (p : Pattern) (ha : d307967 p = 1) (hb : d358922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307962 q = 1) (hb : d358917 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d307962, d358917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105832 q ha hb
    | true =>
      simp only [d307962, d358917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307963 q = 1) (hb : d358918 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d307963, d358918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307963, d358918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307964 q = 1) (hb : d358919 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d307964, d358919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307964, d358919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307965 q = 1) (hb : d358920 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d307965, d358920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307965, d358920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307966 q = 1) (hb : d358921 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d307966, d358921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307966, d358921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307967 q = 1) (hb : d358922 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d307967, d358922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307967, d358922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105834 (p : Pattern) (ha : d307973 p = 1) (hb : d358928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307968 q = 1) (hb : d358923 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d307968, d358923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105833 q ha hb
    | true =>
      simp only [d307968, d358923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307969 q = 1) (hb : d358924 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d307969, d358924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307969, d358924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307970 q = 1) (hb : d358925 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d307970, d358925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307970, d358925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307971 q = 1) (hb : d358926 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d307971, d358926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307971, d358926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307972 q = 1) (hb : d358927 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d307972, d358927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307972, d358927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307973 q = 1) (hb : d358928 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d307973, d358928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307973, d358928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro105835 (p : Pattern) (ha : d309809 p = 1) (hb : d357690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357626 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309805 q = 1) (hb : d357686 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309805, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309806 q = 1) (hb : d357687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309806, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309807 q = 1) (hb : d357688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309807, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309808 q = 1) (hb : d357689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309808, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309809 q = 1) (hb : d357690 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309809, d357690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309809, d357690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105836 (p : Pattern) (ha : d309814 p = 1) (hb : d357697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d357626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309805 q = 1) (hb : d357686 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309805, d357686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309806 q = 1) (hb : d357687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309806, d357687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309807 q = 1) (hb : d357688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309807, d357688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309808 q = 1) (hb : d357689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309808, d357689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42445 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d357633 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309810 q = 1) (hb : d357693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309810, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309811 q = 1) (hb : d357694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309811, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309812 q = 1) (hb : d357695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309812, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309812, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309813 q = 1) (hb : d357696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309813, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309813, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309814 q = 1) (hb : d357697 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309814, d357697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309814, d357697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105837 (p : Pattern) (ha : d309821 p = 1) (hb : d358777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357633 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309810 q = 1) (hb : d357693 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309810, d357693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309811 q = 1) (hb : d357694 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309811, d357694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309819 q = 1) (hb : d357695 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309819, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309819, d357695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309820 q = 1) (hb : d357696 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309820, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309820, d357696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309821 q = 1) (hb : d358777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309821, d358777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309821, d358777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105838 (p : Pattern) (ha : d309831 p = 1) (hb : d358787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357669 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309827 q = 1) (hb : d358783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309827, d358783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309827, d358783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42521 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309828 q = 1) (hb : d358784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309828, d358784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309828, d358784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309829 q = 1) (hb : d358785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309829, d358785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309829, d358785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309830 q = 1) (hb : d358786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309830, d358786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309830, d358786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309831 q = 1) (hb : d358787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309831, d358787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309831, d358787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105839 (p : Pattern) (ha : d309837 p = 1) (hb : d358793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309815 q = 1) (hb : d357698 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309815, d357698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105835 q ha hb
    | true =>
      simp only [d309815, d357698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105836 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309816 q = 1) (hb : d357699 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309816, d357699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309816, d357699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309817 q = 1) (hb : d358775 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309817, d358775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309817, d358775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309818 q = 1) (hb : d358776 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309818, d358776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309818, d358776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309822 q = 1) (hb : d358778 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309822, d358778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309822, d358778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105837 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309823 q = 1) (hb : d358779 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309823, d358779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309823, d358779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309824 q = 1) (hb : d358780 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309824, d358780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309824, d358780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309825 q = 1) (hb : d358781 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309825, d358781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309825, d358781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309826 q = 1) (hb : d358782 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309826, d358782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309826, d358782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309832 q = 1) (hb : d358788 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309832, d358788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309832, d358788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105838 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309833 q = 1) (hb : d358789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309833, d358789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309833, d358789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309834 q = 1) (hb : d358790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309834, d358790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309834, d358790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309835 q = 1) (hb : d358791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309835, d358791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309835, d358791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309836 q = 1) (hb : d358792 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309836, d358792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309836, d358792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309837 q = 1) (hb : d358793 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309837, d358793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309837, d358793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105840 (p : Pattern) (ha : d309843 p = 1) (hb : d358799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d309800 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d309800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d309800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80535 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d309801 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d309801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d309801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d309802 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d309802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d309802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d309803 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d309803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d309803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d309804 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d309804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d309804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309838 q = 1) (hb : d358794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309838, d358794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309838, d358794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105839 q ha hb
  have h8 (q : Pattern) (ha : d309839 q = 1) (hb : d358795 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309839, d358795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309839, d358795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309840 q = 1) (hb : d358796 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309840, d358796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309840, d358796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309841 q = 1) (hb : d358797 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309841, d358797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309841, d358797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309842 q = 1) (hb : d358798 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309842, d358798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309842, d358798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d309843 q = 1) (hb : d358799 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d358799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d309843, d358799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro105841 (p : Pattern) (ha : d309848 p = 1) (hb : d357861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357856 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309844 q = 1) (hb : d357857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309844, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309845 q = 1) (hb : d357858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309845, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309846 q = 1) (hb : d357859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309846, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309847 q = 1) (hb : d357860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309847, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309848 q = 1) (hb : d357861 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309848, d357861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309848, d357861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105842 (p : Pattern) (ha : d309853 p = 1) (hb : d357871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d357856 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309844 q = 1) (hb : d357857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309844, d357857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309845 q = 1) (hb : d357858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309845, d357858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309846 q = 1) (hb : d357859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309846, d357859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309847 q = 1) (hb : d357860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309847, d357860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42705 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42710 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d357866 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309849 q = 1) (hb : d357867 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309849, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309850 q = 1) (hb : d357868 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309850, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309851 q = 1) (hb : d357869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309851, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309851, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309852 q = 1) (hb : d357870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309852, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309852, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309853 q = 1) (hb : d357871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309853, d357871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309853, d357871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105843 (p : Pattern) (ha : d309860 p = 1) (hb : d358802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309849 q = 1) (hb : d357867 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309849, d357867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309850 q = 1) (hb : d357868 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309850, d357868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309858 q = 1) (hb : d357869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309858, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309858, d357869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309859 q = 1) (hb : d357870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309859, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309859, d357870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309860 q = 1) (hb : d358802 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309860, d358802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309860, d358802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105844 (p : Pattern) (ha : d309870 p = 1) (hb : d358813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d358808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309866 q = 1) (hb : d358809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309866, d358809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309866, d358809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309867 q = 1) (hb : d358810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309867, d358810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309867, d358810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309868 q = 1) (hb : d358811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309868, d358811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309868, d358811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309869 q = 1) (hb : d358812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309869, d358812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309869, d358812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309870 q = 1) (hb : d358813 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309870, d358813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309870, d358813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105845 (p : Pattern) (ha : d309876 p = 1) (hb : d358819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309854 q = 1) (hb : d357872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309854, d357872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105841 q ha hb
    | true =>
      simp only [d309854, d357872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105842 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309855 q = 1) (hb : d357873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309855, d357873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309855, d357873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309856 q = 1) (hb : d358800 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309856, d358800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309856, d358800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309857 q = 1) (hb : d358801 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309857, d358801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309857, d358801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309861 q = 1) (hb : d358803 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309861, d358803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309861, d358803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105843 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d42746 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309862 q = 1) (hb : d358804 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309862, d358804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309862, d358804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309863 q = 1) (hb : d358805 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309863, d358805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309863, d358805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309864 q = 1) (hb : d358806 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309864, d358806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309864, d358806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309865 q = 1) (hb : d358807 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309865, d358807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309865, d358807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309871 q = 1) (hb : d358814 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309871, d358814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309871, d358814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105844 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42851 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309872 q = 1) (hb : d358815 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309872, d358815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309872, d358815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309873 q = 1) (hb : d358816 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309873, d358816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309873, d358816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309874 q = 1) (hb : d358817 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309874, d358817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309874, d358817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309875 q = 1) (hb : d358818 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309875, d358818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309875, d358818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309876 q = 1) (hb : d358819 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309876, d358819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309876, d358819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105846 (p : Pattern) (ha : d309882 p = 1) (hb : d358825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309877 q = 1) (hb : d358820 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309877, d358820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309877, d358820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105845 q ha hb
  have h2 (q : Pattern) (ha : d309878 q = 1) (hb : d358821 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309878, d358821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309878, d358821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309879 q = 1) (hb : d358822 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309879, d358822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309879, d358822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309880 q = 1) (hb : d358823 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309880, d358823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309880, d358823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309881 q = 1) (hb : d358824 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309881, d358824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309881, d358824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309882 q = 1) (hb : d358825 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309882, d358825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309882, d358825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105847 (p : Pattern) (ha : d309888 p = 1) (hb : d358121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d358116 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309884 q = 1) (hb : d358117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309884, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309885 q = 1) (hb : d358118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309885, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309886 q = 1) (hb : d358119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309886, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309887 q = 1) (hb : d358120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309887, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309888 q = 1) (hb : d358121 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309888, d358121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309888, d358121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105848 (p : Pattern) (ha : d309893 p = 1) (hb : d358131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d358116 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309884 q = 1) (hb : d358117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309884, d358117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309885 q = 1) (hb : d358118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309885, d358118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309886 q = 1) (hb : d358119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309886, d358119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309887 q = 1) (hb : d358120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309887, d358120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43091 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d358126 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309889 q = 1) (hb : d358127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309889, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309890 q = 1) (hb : d358128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309890, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309891 q = 1) (hb : d358129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309891, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309891, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309892 q = 1) (hb : d358130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309892, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309892, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309893 q = 1) (hb : d358131 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309893, d358131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309893, d358131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105849 (p : Pattern) (ha : d309900 p = 1) (hb : d358829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d358126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309889 q = 1) (hb : d358127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309889, d358127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309890 q = 1) (hb : d358128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309890, d358128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309898 q = 1) (hb : d358129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309898, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309898, d358129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309899 q = 1) (hb : d358130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309899, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309899, d358130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309900 q = 1) (hb : d358829 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309900, d358829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309900, d358829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105850 (p : Pattern) (ha : d309910 p = 1) (hb : d358840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d358835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309906 q = 1) (hb : d358836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309906, d358836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309906, d358836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43248 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309907 q = 1) (hb : d358837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309907, d358837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309907, d358837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309908 q = 1) (hb : d358838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309908, d358838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309908, d358838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309909 q = 1) (hb : d358839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309909, d358839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309909, d358839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309910 q = 1) (hb : d358840 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309910, d358840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309910, d358840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105851 (p : Pattern) (ha : d309916 p = 1) (hb : d358846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309894 q = 1) (hb : d358132 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309894, d358132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105847 q ha hb
    | true =>
      simp only [d309894, d358132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105848 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309895 q = 1) (hb : d358133 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309895, d358133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309895, d358133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309896 q = 1) (hb : d358827 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309896, d358827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309896, d358827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309897 q = 1) (hb : d358828 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309897, d358828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309897, d358828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309901 q = 1) (hb : d358830 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309901, d358830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309901, d358830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105849 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43127 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309902 q = 1) (hb : d358831 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309902, d358831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309902, d358831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309903 q = 1) (hb : d358832 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309903, d358832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309903, d358832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309904 q = 1) (hb : d358833 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309904, d358833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309904, d358833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309905 q = 1) (hb : d358834 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309905, d358834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309905, d358834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309911 q = 1) (hb : d358841 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309911, d358841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309911, d358841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105850 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43264 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309912 q = 1) (hb : d358842 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309912, d358842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309912, d358842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309913 q = 1) (hb : d358843 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309913, d358843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309913, d358843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309914 q = 1) (hb : d358844 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309914, d358844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309914, d358844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309915 q = 1) (hb : d358845 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309915, d358845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309915, d358845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309916 q = 1) (hb : d358846 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309916, d358846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309916, d358846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105852 (p : Pattern) (ha : d309922 p = 1) (hb : d358852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309917 q = 1) (hb : d358847 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309917, d358847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309917, d358847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105851 q ha hb
  have h2 (q : Pattern) (ha : d309918 q = 1) (hb : d358848 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309918, d358848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309918, d358848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309919 q = 1) (hb : d358849 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309919, d358849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309919, d358849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309920 q = 1) (hb : d358850 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309920, d358850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309920, d358850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309921 q = 1) (hb : d358851 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309921, d358851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309921, d358851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309922 q = 1) (hb : d358852 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309922, d358852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309922, d358852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105853 (p : Pattern) (ha : d309929 p = 1) (hb : d358458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d358453 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309925 q = 1) (hb : d358454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d358454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309925, d358454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309926 q = 1) (hb : d358455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d358455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309926, d358455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d309927 q = 1) (hb : d358456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d358456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309927, d358456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309928 q = 1) (hb : d358457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d358457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309928, d358457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309929 q = 1) (hb : d358458 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309929, d358458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309929, d358458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105854 (p : Pattern) (ha : d309934 p = 1) (hb : d358468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d358453 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309925 q = 1) (hb : d358454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309925, d358454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309925, d358454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309926 q = 1) (hb : d358455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309926, d358455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309926, d358455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d309927 q = 1) (hb : d358456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309927, d358456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309927, d358456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309928 q = 1) (hb : d358457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309928, d358457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309928, d358457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43605 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43610 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d358463 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309930 q = 1) (hb : d358464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309930, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309931 q = 1) (hb : d358465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309931, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309932 q = 1) (hb : d358466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309932, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309932, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309933 q = 1) (hb : d358467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309933, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309933, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309934 q = 1) (hb : d358468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309934, d358468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309934, d358468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105855 (p : Pattern) (ha : d309941 p = 1) (hb : d358857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d358463 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309930 q = 1) (hb : d358464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309930, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309930, d358464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309931 q = 1) (hb : d358465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309931, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309931, d358465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309939 q = 1) (hb : d358466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309939, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309939, d358466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309940 q = 1) (hb : d358467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309940, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309940, d358467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309941 q = 1) (hb : d358857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309941, d358857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309941, d358857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105856 (p : Pattern) (ha : d309951 p = 1) (hb : d358868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d358863 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309947 q = 1) (hb : d358864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309947, d358864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309947, d358864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309948 q = 1) (hb : d358865 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309948, d358865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309948, d358865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309949 q = 1) (hb : d358866 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309949, d358866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309949, d358866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309950 q = 1) (hb : d358867 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309950, d358867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309950, d358867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309951 q = 1) (hb : d358868 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309951, d358868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309951, d358868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105857 (p : Pattern) (ha : d309957 p = 1) (hb : d358874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309935 q = 1) (hb : d358469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309935, d358469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105853 q ha hb
    | true =>
      simp only [d309935, d358469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105854 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309936 q = 1) (hb : d358470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309936, d358470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309936, d358470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309937 q = 1) (hb : d358855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309937, d358855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309937, d358855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309938 q = 1) (hb : d358856 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309938, d358856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309938, d358856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309942 q = 1) (hb : d358858 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309942, d358858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309942, d358858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105855 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43646 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309943 q = 1) (hb : d358859 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309943, d358859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309943, d358859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309944 q = 1) (hb : d358860 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309944, d358860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309944, d358860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309945 q = 1) (hb : d358861 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309945, d358861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309945, d358861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309946 q = 1) (hb : d358862 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309946, d358862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309946, d358862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309952 q = 1) (hb : d358869 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309952, d358869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309952, d358869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105856 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309953 q = 1) (hb : d358870 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309953, d358870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309953, d358870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309954 q = 1) (hb : d358871 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309954, d358871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309954, d358871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309955 q = 1) (hb : d358872 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309955, d358872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309955, d358872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309956 q = 1) (hb : d358873 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309956, d358873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309956, d358873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309957 q = 1) (hb : d358874 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309957, d358874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309957, d358874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105858 (p : Pattern) (ha : d309963 p = 1) (hb : d358880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309958 q = 1) (hb : d358875 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309958, d358875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309958, d358875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105857 q ha hb
  have h2 (q : Pattern) (ha : d309959 q = 1) (hb : d358876 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309959, d358876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309959, d358876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309960 q = 1) (hb : d358877 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309960, d358877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309960, d358877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309961 q = 1) (hb : d358878 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309961, d358878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309961, d358878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309962 q = 1) (hb : d358879 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309962, d358879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309962, d358879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309963 q = 1) (hb : d358880 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309963, d358880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309963, d358880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105859 (p : Pattern) (ha : d46527 p = 1) (hb : d309971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46523 q = 1) (hb : d309967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d309967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46523, d309967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46524 q = 1) (hb : d309968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d309968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46524, d309968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46525 q = 1) (hb : d309969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d309969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46525, d309969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46526 q = 1) (hb : d309970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d309970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46526, d309970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46527 q = 1) (hb : d309971 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, d309971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46527, d309971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105860 (p : Pattern) (ha : d46537 p = 1) (hb : d309976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46523 q = 1) (hb : d309967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d309967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46523, d309967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46524 q = 1) (hb : d309968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d309968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46524, d309968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46525 q = 1) (hb : d309969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d309969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46525, d309969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46526 q = 1) (hb : d309970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d309970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d309970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d44191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d44196 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46532 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46533 q = 1) (hb : d309972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d309972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46533, d309972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46534 q = 1) (hb : d309973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d309973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46534, d309973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46535 q = 1) (hb : d309974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d309974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46535, d309974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46536 q = 1) (hb : d309975 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d309975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46536, d309975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46537 q = 1) (hb : d309976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, d309976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46537, d309976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro105861 (p : Pattern) (ha : d309983 p = 1) (hb : d321880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46532 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46533 q = 1) (hb : d309972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d309972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46533, d309972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46534 q = 1) (hb : d309973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d309973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46534, d309973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46535 q = 1) (hb : d309981 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d309981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d309981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46536 q = 1) (hb : d309982 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d309982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d309982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309983 q = 1) (hb : d321880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309983, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309983, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro105862 (p : Pattern) (ha : d309993 p = 1) (hb : d321891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309989 q = 1) (hb : d321887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309989, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309989, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44409 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309990 q = 1) (hb : d321888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309990, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309990, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309991 q = 1) (hb : d321889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309991, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309991, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309992 q = 1) (hb : d321890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309992, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309992, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309993 q = 1) (hb : d321891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309993, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309993, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105863 (p : Pattern) (ha : d309999 p = 1) (hb : d321897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d309977 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d309977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105859 q ha hb
    | true =>
      simp only [d46538, d309977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105860 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46539 q = 1) (hb : d309978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d309978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, d309978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309979 q = 1) (hb : d321878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309979, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309979, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309980 q = 1) (hb : d321879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309980, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309980, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309984 q = 1) (hb : d321881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309984, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309984, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105861 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d44232 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309985 q = 1) (hb : d321882 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309985, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309985, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309986 q = 1) (hb : d321883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309986, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309986, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309987 q = 1) (hb : d321884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309987, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309987, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309988 q = 1) (hb : d321885 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309988, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309988, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309994 q = 1) (hb : d321892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309994, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309994, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105862 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44425 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309995 q = 1) (hb : d321893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309995, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309995, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309996 q = 1) (hb : d321894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309996, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309996, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309997 q = 1) (hb : d321895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309997, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309997, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309998 q = 1) (hb : d321896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309998, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309998, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309999 q = 1) (hb : d321897 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309999, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309999, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105864 (p : Pattern) (ha : d310005 p = 1) (hb : d321903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310000 q = 1) (hb : d321898 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d310000, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310000, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105863 q ha hb
  have h2 (q : Pattern) (ha : d310001 q = 1) (hb : d321899 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d310001, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310001, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d310002 q = 1) (hb : d321900 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d310002, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310002, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d310003 q = 1) (hb : d321901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d310003, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310003, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d310004 q = 1) (hb : d321902 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d310004, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310004, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d310005 q = 1) (hb : d321903 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d310005, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d310005, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105865 (p : Pattern) (ha : d310011 p = 1) (hb : d358886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d309883 q = 1) (hb : d358826 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d358826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105840 q ha hb
    | true =>
      simp only [d309883, d358826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105846 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309923 q = 1) (hb : d358853 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309923, d358853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309923, d358853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105852 q ha hb
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d358854 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d358854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309924, d358854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309964 q = 1) (hb : d358881 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309964, d358881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309964, d358881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105858 q ha hb
  have h5 (q : Pattern) (ha : d309965 q = 1) (hb : d358882 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309965, d358882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309965, d358882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309966 q = 1) (hb : d358883 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d358883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d358883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d310006 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d310006, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310006, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105864 q ha hb
  have h8 (q : Pattern) (ha : d310007 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d310007, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310007, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d310008 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d310008, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310008, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d310009 q = 1) (hb : d358884 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d358884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d310009, d358884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d310010 q = 1) (hb : d358885 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d358885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d310010, d358885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d310011 q = 1) (hb : d358886 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d358886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d310011, d358886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h13 p ha hb
theorem andIntro105866 (p : Pattern) (ha : d310017 p = 1) (hb : d358892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d358887 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d358887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105865 q ha hb
    | true =>
      simp only [d310012, d358887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d358888 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d358888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d358888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d358889 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d358889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d358889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d358890 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d358890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d358890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d358891 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d358891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d358891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d358892 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d358892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d358892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105867 (p : Pattern) (ha : d310023 p = 1) (hb : d358898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d358893 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d358893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105866 q ha hb
    | true =>
      simp only [d310018, d358893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d358894 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d358894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d358894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d358895 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d358895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d358895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d358896 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d358896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d358896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d358897 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d358897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d358897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310023 q = 1) (hb : d358898 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d358898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, d358898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105868 (p : Pattern) (ha : d310029 p = 1) (hb : d358904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d358899 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d358899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105867 q ha hb
    | true =>
      simp only [d310024, d358899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d358900 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d358900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d358900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d358901 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d358901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d358901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d358902 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d358902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d358902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d358903 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d358903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d358903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d358904 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d358904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d358904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105869 (p : Pattern) (ha : d310035 p = 1) (hb : d358910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d358905 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d358905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105868 q ha hb
    | true =>
      simp only [d310030, d358905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d358906 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d358906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d358906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d358907 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d358907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d358907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d358908 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d358908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d358908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d358909 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d358909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d358909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d358910 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d358910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d358910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105870 (p : Pattern) (ha : d310041 p = 1) (hb : d358916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d358911 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d358911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105869 q ha hb
    | true =>
      simp only [d310036, d358911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d358912 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d358912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d358912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d358913 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d358913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d358913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d358914 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d358914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d358914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d358915 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d358915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d358915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d358916 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d358916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d358916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105871 (p : Pattern) (ha : d310047 p = 1) (hb : d358922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d358917 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d358917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105870 q ha hb
    | true =>
      simp only [d310042, d358917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d358918 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d358918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d358918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d358919 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d358919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d358919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d358920 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d358920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d358920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d358921 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d358921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d358921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d358922 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d358922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d358922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105872 (p : Pattern) (ha : d310053 p = 1) (hb : d358928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d358923 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d358923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105871 q ha hb
    | true =>
      simp only [d310048, d358923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d358924 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d358924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d358924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d358925 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d358925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d358925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d358926 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d358926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d358926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d358927 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d358927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d358927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d358928 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d358928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d358928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105873 (p : Pattern) (ha : d9771 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1084 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1084, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1085 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1086 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9771 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d9771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro105874 (p : Pattern) (ha : d46460 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1084 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1084, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d44996 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46459 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46460 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105875 (p : Pattern) (ha : d46466 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105874 q ha hb
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105873 q ha hb
  have h3 (q : Pattern) (ha : d46462 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46463 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46464 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46465 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46466 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro105876 (p : Pattern) (ha : d46473 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45587 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46472 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46473 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro105877 (p : Pattern) (ha : d46482 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105874 q ha hb
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105873 q ha hb
  have h3 (q : Pattern) (ha : d46462 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46463 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46464 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46465 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46474 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105876 q ha hb
  have h8 (q : Pattern) (ha : d1115 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
  have h9 (q : Pattern) (ha : d46475 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46476 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46477 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105876 q ha hb
    | true =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46478 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46479 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46480 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46481 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d46482 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro105878 (p : Pattern) (ha : d46488 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46467 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46468 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46469 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46470 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46471 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46483 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46484 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46485 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46486 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46487 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46488 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105879 (p : Pattern) (ha : d46490 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46467 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46468 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46469 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46470 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46483 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46484 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46485 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46486 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46487 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46489 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46490 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105880 (p : Pattern) (ha : d46494 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46474 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105876 q ha hb
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
  have h3 (q : Pattern) (ha : d46475 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46476 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46477 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105876 q ha hb
    | true =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46478 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46479 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46480 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46481 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46494 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro105881 (p : Pattern) (ha : d46500 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46483 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46484 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46485 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46486 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46489 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46495 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105880 q ha hb
    | true =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46496 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46497 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46498 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46499 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46500 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105882 (p : Pattern) (ha : d46507 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46491 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105878 q ha hb
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105879 q ha hb
  have h2 (q : Pattern) (ha : d46492 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46493 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46501 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105879 q ha hb
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105881 q ha hb
  have h5 (q : Pattern) (ha : d46502 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46503 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46504 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46505 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46506 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46507 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105883 (p : Pattern) (ha : d46511 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46501 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105879 q ha hb
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105881 q ha hb
  have h2 (q : Pattern) (ha : d46502 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46503 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46505 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46510 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46511 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105884 (p : Pattern) (ha : d46517 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105882 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46515 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46516 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46517 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105885 (p : Pattern) (ha : d46521 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46519 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46520 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46521 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105886 (p : Pattern) (ha : d46527 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46522 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105884 q ha hb
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105885 q ha hb
  have h2 (q : Pattern) (ha : d46523 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46524 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46525 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46526 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46527 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105887 (p : Pattern) (ha : d46530 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105882 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46515 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46516 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46530 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105888 (p : Pattern) (ha : d46531 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46519 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46520 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46531 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105889 (p : Pattern) (ha : d46537 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46522 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105884 q ha hb
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105885 q ha hb
  have h2 (q : Pattern) (ha : d46523 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46524 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46525 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46526 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46532 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105887 q ha hb
    | true =>
      simp only [d46532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105888 q ha hb
  have h7 (q : Pattern) (ha : d46533 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46534 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46535 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46536 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46537 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105890 (p : Pattern) (ha : d46693 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46522 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105884 q ha hb
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105885 q ha hb
  have h2 (q : Pattern) (ha : d46523 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46524 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46525 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46526 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46688 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105885 q ha hb
    | true =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46689 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46690 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46691 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46692 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46693 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105891 (p : Pattern) (ha : d46699 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46688 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105885 q ha hb
    | true =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46689 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46690 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46691 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46692 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46694 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105888 q ha hb
    | true =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46695 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46696 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46697 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46698 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46699 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105892 (p : Pattern) (ha : d46708 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46694 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105888 q ha hb
    | true =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46695 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46696 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46697 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46698 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46708 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105893 (p : Pattern) (ha : d46730 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46714 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
  have h2 (q : Pattern) (ha : d46467 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46715 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46468 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46716 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46717 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46720 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
  have h8 (q : Pattern) (ha : d46483 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46721 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46484 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46722 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46723 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46724 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46729 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46730 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105894 (p : Pattern) (ha : d46740 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46720 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
  have h2 (q : Pattern) (ha : d46483 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46721 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46484 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46722 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46723 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46729 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46735 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105880 q ha hb
  have h9 (q : Pattern) (ha : d46495 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105880 q ha hb
    | true =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46736 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46496 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46737 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46738 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d46739 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46740 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105895 (p : Pattern) (ha : d46759 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46741 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105893 q ha hb
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105894 q ha hb
  have h2 (q : Pattern) (ha : d46742 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46743 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46749 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46758 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46759 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105896 (p : Pattern) (ha : d46841 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46760 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105895 q ha hb
    | true =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46761 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46838 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46839 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46840 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46841 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105897 (p : Pattern) (ha : d46847 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46842 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105896 q ha hb
    | true =>
      simp only [d46842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46843 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46844 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46845 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46846 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46847 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105898 (p : Pattern) (ha : d46542 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105882 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46515 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46541 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46542 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105899 (p : Pattern) (ha : d46544 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46519 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46543 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46544 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105900 (p : Pattern) (ha : d46551 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105882 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46549 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46550 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46551 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105901 (p : Pattern) (ha : d46554 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46552 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46553 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46554 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105902 (p : Pattern) (ha : d46558 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46467 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46468 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46469 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46470 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46471 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46558 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105903 (p : Pattern) (ha : d46564 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46559 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105902 q ha hb
    | true =>
      simp only [d46559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105878 q ha hb
  have h2 (q : Pattern) (ha : d46560 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46561 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46491 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105878 q ha hb
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105879 q ha hb
  have h5 (q : Pattern) (ha : d46492 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46493 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46562 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46501 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105879 q ha hb
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105881 q ha hb
  have h9 (q : Pattern) (ha : d46502 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46503 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46504 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46563 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46564 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105904 (p : Pattern) (ha : d46570 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46565 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105903 q ha hb
    | true =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46566 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46508 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105882 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46509 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46567 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46568 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46569 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46570 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105905 (p : Pattern) (ha : d46637 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46461 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105874 q ha hb
  have h2 (q : Pattern) (ha : d32155 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105873 q ha hb
  have h3 (q : Pattern) (ha : d46462 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46463 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46464 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46465 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46637 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro105906 (p : Pattern) (ha : d46643 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46467 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46468 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46469 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46470 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46483 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46484 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46485 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46486 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46487 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46638 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105905 q ha hb
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46639 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46640 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46641 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d46642 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d46643 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105907 (p : Pattern) (ha : d46644 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46638 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105905 q ha hb
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46639 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46640 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46641 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46642 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46644 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105908 (p : Pattern) (ha : d46650 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46491 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105878 q ha hb
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105879 q ha hb
  have h2 (q : Pattern) (ha : d46492 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46493 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46501 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105879 q ha hb
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105881 q ha hb
  have h5 (q : Pattern) (ha : d46502 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46503 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46504 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46645 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105906 q ha hb
    | true =>
      simp only [d46645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105907 q ha hb
  have h9 (q : Pattern) (ha : d46646 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46647 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46648 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46649 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46650 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105909 (p : Pattern) (ha : d46656 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46651 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105908 q ha hb
    | true =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46652 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46653 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46654 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46655 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46656 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105910 (p : Pattern) (ha : d46864 p = 1) (hb : d321643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46545 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105898 q ha hb
    | true =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105899 q ha hb
  have h2 (q : Pattern) (ha : d46546 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46547 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46548 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46555 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105900 q ha hb
    | true =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105901 q ha hb
  have h6 (q : Pattern) (ha : d46556 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46557 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46571 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105904 q ha hb
    | true =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105884 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d321639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46657 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105909 q ha hb
    | true =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46658 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d321640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d321641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d321642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d321643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105911 (p : Pattern) (ha : d46663 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105882 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46515 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46541 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46663 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105912 (p : Pattern) (ha : d46664 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46519 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46543 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46664 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105913 (p : Pattern) (ha : d46669 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46508 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105882 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46509 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46514 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46549 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46550 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46669 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105914 (p : Pattern) (ha : d46670 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46512 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105883 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46513 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46518 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46552 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46553 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46670 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105915 (p : Pattern) (ha : d46674 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46565 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105903 q ha hb
    | true =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46566 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46508 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105882 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46509 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46567 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46568 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46569 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46674 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105916 (p : Pattern) (ha : d46680 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46651 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105908 q ha hb
    | true =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46652 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46653 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46654 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46655 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46680 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105917 (p : Pattern) (ha : d46864 p = 1) (hb : d321648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46545 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105898 q ha hb
    | true =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105899 q ha hb
  have h2 (q : Pattern) (ha : d46546 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46547 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46548 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46555 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105900 q ha hb
    | true =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105901 q ha hb
  have h6 (q : Pattern) (ha : d46556 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46557 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46571 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105904 q ha hb
    | true =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105884 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d321639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46657 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105909 q ha hb
    | true =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46658 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d321640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d321641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d321642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46665 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105911 q ha hb
    | true =>
      simp only [d46665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105912 q ha hb
  have h16 (q : Pattern) (ha : d46666 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46667 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46668 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46671 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105913 q ha hb
    | true =>
      simp only [d46671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105914 q ha hb
  have h20 (q : Pattern) (ha : d46672 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d46673 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d46673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d46675 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105915 q ha hb
    | true =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105887 q ha hb
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d321644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d46681 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105916 q ha hb
    | true =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d46682 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46864 q = 1) (hb : d321645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d46864 q = 1) (hb : d321646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d321646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d46864 q = 1) (hb : d321647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d321647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d46864 q = 1) (hb : d321648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d321648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro105918 (p : Pattern) (ha : d46864 p = 1) (hb : d321655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46675 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105915 q ha hb
    | true =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105887 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d321644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46681 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105916 q ha hb
    | true =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46682 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d321645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d321653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d321654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d321655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105919 (p : Pattern) (ha : d46719 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46714 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
  have h2 (q : Pattern) (ha : d46467 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46715 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46468 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46716 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46717 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46718 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46719 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105920 (p : Pattern) (ha : d46725 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46714 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
  have h2 (q : Pattern) (ha : d46467 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46715 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46468 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46716 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46717 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46718 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46720 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
  have h9 (q : Pattern) (ha : d46483 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d46721 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46484 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46722 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46723 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d46724 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46725 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105921 (p : Pattern) (ha : d46746 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46726 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105919 q ha hb
    | true =>
      simp only [d46726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105920 q ha hb
  have h2 (q : Pattern) (ha : d46727 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46728 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46731 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105920 q ha hb
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105893 q ha hb
  have h5 (q : Pattern) (ha : d46732 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46733 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46734 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46741 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105893 q ha hb
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105894 q ha hb
  have h9 (q : Pattern) (ha : d46742 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46743 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46744 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46745 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46746 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105922 (p : Pattern) (ha : d46751 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46731 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105920 q ha hb
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105893 q ha hb
  have h2 (q : Pattern) (ha : d46732 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46733 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46741 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105893 q ha hb
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105894 q ha hb
  have h5 (q : Pattern) (ha : d46742 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46743 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46744 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46749 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46750 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46751 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105923 (p : Pattern) (ha : d46757 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46747 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105921 q ha hb
    | true =>
      simp only [d46747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46748 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46752 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105922 q ha hb
    | true =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46753 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46754 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46755 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46756 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46757 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105924 (p : Pattern) (ha : d46765 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46752 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105922 q ha hb
    | true =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46753 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46760 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105895 q ha hb
    | true =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46761 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46762 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46763 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46764 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46765 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105925 (p : Pattern) (ha : d46817 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46714 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
  have h2 (q : Pattern) (ha : d46467 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105875 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46715 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46468 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46716 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46717 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46720 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
  have h8 (q : Pattern) (ha : d46483 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105877 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d46721 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46484 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d46722 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46723 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d46724 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46812 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105905 q ha hb
  have h15 (q : Pattern) (ha : d46638 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105905 q ha hb
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d46813 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46639 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d46814 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d46815 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d46816 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d46817 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro105926 (p : Pattern) (ha : d46818 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46812 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105905 q ha hb
  have h2 (q : Pattern) (ha : d46638 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105905 q ha hb
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46813 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46639 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46814 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46815 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d46816 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46818 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105927 (p : Pattern) (ha : d46824 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46731 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105920 q ha hb
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105893 q ha hb
  have h2 (q : Pattern) (ha : d46732 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46733 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46741 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105893 q ha hb
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105894 q ha hb
  have h5 (q : Pattern) (ha : d46742 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46743 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46744 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46819 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105925 q ha hb
    | true =>
      simp only [d46819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105926 q ha hb
  have h9 (q : Pattern) (ha : d46820 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46821 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46822 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46823 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46824 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105928 (p : Pattern) (ha : d46830 p = 1) (hb : d46864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46825 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105927 q ha hb
    | true =>
      simp only [d46825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d46826 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46827 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46828 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46829 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d46830 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105929 (p : Pattern) (ha : d46864 p = 1) (hb : d321665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46766 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105923 q ha hb
    | true =>
      simp only [d46766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105924 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d321661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d321661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d46831 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105928 q ha hb
    | true =>
      simp only [d46831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46832 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d321662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d321663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d321664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d321665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105930 (p : Pattern) (ha : d46864 p = 1) (hb : d321671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46528 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105886 q ha hb
  have h2 (q : Pattern) (ha : d46529 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d46538 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105886 q ha hb
    | true =>
      simp only [d46538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105889 q ha hb
  have h4 (q : Pattern) (ha : d46539 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46540 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d321649 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105910 q ha hb
    | true =>
      simp only [d321649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105917 q ha hb
  have h7 (q : Pattern) (ha : d46700 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105890 q ha hb
    | true =>
      simp only [d46700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105891 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d321650 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d321651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d321651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d321652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d321652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d321656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105918 q ha hb
  have h12 (q : Pattern) (ha : d46709 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105892 q ha hb
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d321657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d321657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d321658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d321659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d321659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d46864 q = 1) (hb : d321660 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46864 q = 1) (hb : d321666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105929 q ha hb
  have h18 (q : Pattern) (ha : d46848 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105897 q ha hb
  have h19 (q : Pattern) (ha : d46864 q = 1) (hb : d321667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d46864 q = 1) (hb : d321668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d321668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d46864 q = 1) (hb : d321669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d321669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d46864 q = 1) (hb : d321670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d321670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d321671 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro105931 (p : Pattern) (ha : d46864 p = 1) (hb : d321677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46864 q = 1) (hb : d321672 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105930 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d321673 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d46864 q = 1) (hb : d321674 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d321675 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d321676 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d321677 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105932 (p : Pattern) (ha : d44884 p = 1) (hb : d46864 p = 1) : d46867 p = 1 := by
  have h0 (q : Pattern) (ha : d44881 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44882 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44882, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44882, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d16 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44883 q = 1) (hb : d46864 q = 1) : d46866 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44883, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44883, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h10 (q : Pattern) (ha : d44884 q = 1) (hb : d46864 q = 1) : d46867 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44884, d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44884, d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro105933 (p : Pattern) (ha : d44890 p = 1) (hb : d46864 p = 1) : d355780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44885 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105932 q ha hb
    | true =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44886 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44887 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44888 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44888, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44889 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44889, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44890 q = 1) (hb : d46864 q = 1) : d355780 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44890, d355780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44890, d355780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105934 (p : Pattern) (ha : d44896 p = 1) (hb : d46864 p = 1) : d355786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44891 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105933 q ha hb
    | true =>
      simp only [d44891, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44892 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44892, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44893 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44893, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44893, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44894 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44894, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44894, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44895 q = 1) (hb : d46864 q = 1) : d355785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44895, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44895, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44896 q = 1) (hb : d46864 q = 1) : d355786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44896, d355786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44896, d355786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105935 (p : Pattern) (ha : d44902 p = 1) (hb : d46864 p = 1) : d355792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44897 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105934 q ha hb
    | true =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h2 (q : Pattern) (ha : d44898 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44899 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44900 q = 1) (hb : d46864 q = 1) : d355790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44900, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44900, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44901 q = 1) (hb : d46864 q = 1) : d355791 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44901, d355791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44901, d355791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44902 q = 1) (hb : d46864 q = 1) : d355792 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44902, d355792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44902, d355792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105936 (p : Pattern) (ha : d44908 p = 1) (hb : d46864 p = 1) : d355798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44906 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44906, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44907 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44907, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44907, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44908 q = 1) (hb : d46864 q = 1) : d355798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44908, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44908, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105937 (p : Pattern) (ha : d46864 p = 1) (hb : d322010 p = 1) : d355804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96428 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96429 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44909 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105936 q ha hb
    | true =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d322006 q = 1) : d355800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322006, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d322006, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d322007 q = 1) : d355801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322007, d355801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322007, d355801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d322008 q = 1) : d355802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322008, d355802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d322008, d355802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d322009 q = 1) : d355803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322009, d355803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322009, d355803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d322010 q = 1) : d355804 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322010, d355804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322010, d355804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105938 (p : Pattern) (ha : d44915 p = 1) (hb : d46864 p = 1) : d355805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44906 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44906, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44907 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44907, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44907, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44915 q = 1) (hb : d46864 q = 1) : d355805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44915, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44915, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105939 (p : Pattern) (ha : d46864 p = 1) (hb : d322015 p = 1) : d355811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96428 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96429 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44909 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105936 q ha hb
    | true =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d322006 q = 1) : d355800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322006, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d322006, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d322007 q = 1) : d355801 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322007, d355801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322007, d355801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d322008 q = 1) : d355802 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322008, d355802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d322008, d355802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d322009 q = 1) : d355803 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322009, d355803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322009, d355803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96436 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96437 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d44916 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105938 q ha hb
    | true =>
      simp only [d44916, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d322011 q = 1) : d355807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322011, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d322011, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46864 q = 1) (hb : d322012 q = 1) : d355808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322012, d355808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d322012, d355808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d46864 q = 1) (hb : d322013 q = 1) : d355809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322013, d355809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d322013, d355809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d46864 q = 1) (hb : d322014 q = 1) : d355810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322014, d355810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d322014, d355810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d46864 q = 1) (hb : d322015 q = 1) : d355811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322015, d355811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322015, d355811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro105940 (p : Pattern) (ha : d46864 p = 1) (hb : d322022 p = 1) : d355816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44916 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105938 q ha hb
    | true =>
      simp only [d44916, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d322011 q = 1) : d355807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322011, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322011, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d322012 q = 1) : d355808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322012, d355808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322012, d355808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d322020 q = 1) : d355809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322020, d355809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322020, d355809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d322021 q = 1) : d355810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322021, d355810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322021, d355810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d322022 q = 1) : d355816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322022, d355816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322022, d355816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105941 (p : Pattern) (ha : d44939 p = 1) (hb : d46864 p = 1) : d355827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44934 q = 1) (hb : d46864 q = 1) : d355822 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44934, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44934, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105933 q ha hb
  have h2 (q : Pattern) (ha : d44891 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105933 q ha hb
    | true =>
      simp only [d44891, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44935 q = 1) (hb : d46864 q = 1) : d355823 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44935, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44935, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44892 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44892, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44936 q = 1) (hb : d46864 q = 1) : d355824 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44936, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44936, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44937 q = 1) (hb : d46864 q = 1) : d355825 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44937, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44937, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44938 q = 1) (hb : d46864 q = 1) : d355826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44938, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44938, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44939 q = 1) (hb : d46864 q = 1) : d355827 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44939, d355827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44939, d355827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105942 (p : Pattern) (ha : d44945 p = 1) (hb : d46864 p = 1) : d355833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44940 q = 1) (hb : d46864 q = 1) : d355828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105941 q ha hb
    | true =>
      simp only [d44940, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
  have h2 (q : Pattern) (ha : d44941 q = 1) (hb : d46864 q = 1) : d355829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44942 q = 1) (hb : d46864 q = 1) : d355830 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44943 q = 1) (hb : d46864 q = 1) : d355831 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44943, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44943, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44944 q = 1) (hb : d46864 q = 1) : d355832 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44944, d355832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44944, d355832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44945 q = 1) (hb : d46864 q = 1) : d355833 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44945, d355833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44945, d355833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105943 (p : Pattern) (ha : d44951 p = 1) (hb : d46864 p = 1) : d355839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44946 q = 1) (hb : d46864 q = 1) : d355834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105942 q ha hb
    | true =>
      simp only [d44946, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44947 q = 1) (hb : d46864 q = 1) : d355835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96421 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44948 q = 1) (hb : d46864 q = 1) : d355836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44948, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44948, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44949 q = 1) (hb : d46864 q = 1) : d355837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44949, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44949, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44950 q = 1) (hb : d46864 q = 1) : d355838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44950, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44950, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44951 q = 1) (hb : d46864 q = 1) : d355839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44951, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44951, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105944 (p : Pattern) (ha : d46864 p = 1) (hb : d322032 p = 1) : d355845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44952 q = 1) (hb : d46864 q = 1) : d355840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44952, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105943 q ha hb
    | true =>
      simp only [d44952, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96422 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d322028 q = 1) : d355841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322028, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322028, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96422 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d322029 q = 1) : d355842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322029, d355842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322029, d355842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d322030 q = 1) : d355843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322030, d355843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322030, d355843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d322031 q = 1) : d355844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322031, d355844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322031, d355844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d322032 q = 1) : d355845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322032, d355845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322032, d355845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105945 (p : Pattern) (ha : d46864 p = 1) (hb : d322038 p = 1) : d355851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96425 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96425 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96426 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d322016 q = 1) : d355812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322016, d355812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105937 q ha hb
    | true =>
      simp only [d322016, d355812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105939 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96427 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d322017 q = 1) : d355813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322017, d355813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322017, d355813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d322018 q = 1) : d355814 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322018, d355814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d322018, d355814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d322019 q = 1) : d355815 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322019, d355815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d322019, d355815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d322023 q = 1) : d355817 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322023, d355817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322023, d355817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105940 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d322024 q = 1) : d355818 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322024, d355818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d322024, d355818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d322025 q = 1) : d355819 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322025, d355819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d322025, d355819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d322026 q = 1) : d355820 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322026, d355820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322026, d355820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d322027 q = 1) : d355821 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322027, d355821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322027, d355821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46864 q = 1) (hb : d322033 q = 1) : d355846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322033, d355846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322033, d355846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105944 q ha hb
  have h17 (q : Pattern) (ha : d46864 q = 1) (hb : d322034 q = 1) : d355847 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322034, d355847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322034, d355847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d46864 q = 1) (hb : d322035 q = 1) : d355848 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322035, d355848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322035, d355848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d46864 q = 1) (hb : d322036 q = 1) : d355849 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322036, d355849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d322036, d355849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d46864 q = 1) (hb : d322037 q = 1) : d355850 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322037, d355850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d322037, d355850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d46864 q = 1) (hb : d322038 q = 1) : d355851 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322038, d355851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d322038, d355851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro105946 (p : Pattern) (ha : d44973 p = 1) (hb : d46864 p = 1) : d355861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44909 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105936 q ha hb
    | true =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h2 (q : Pattern) (ha : d44969 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44970 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44970, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44971 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44972 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44973 q = 1) (hb : d46864 q = 1) : d355861 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44973, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44973, d355861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105947 (p : Pattern) (ha : d44980 p = 1) (hb : d46864 p = 1) : d355868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44909 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105936 q ha hb
    | true =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h2 (q : Pattern) (ha : d44969 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44970 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44970, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44971 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44972 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44916 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44916, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105938 q ha hb
    | true =>
      simp only [d44916, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96417 q ha hb
  have h7 (q : Pattern) (ha : d44976 q = 1) (hb : d46864 q = 1) : d355864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44976, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44976, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44977 q = 1) (hb : d46864 q = 1) : d355865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44977, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44977, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44978 q = 1) (hb : d46864 q = 1) : d355866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44978, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44978, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44979 q = 1) (hb : d46864 q = 1) : d355867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44979, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44979, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44980 q = 1) (hb : d46864 q = 1) : d355868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44980, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44980, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105948 (p : Pattern) (ha : d45094 p = 1) (hb : d46864 p = 1) : d355933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44909 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105936 q ha hb
    | true =>
      simp only [d44909, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
  have h2 (q : Pattern) (ha : d44969 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44969, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44969, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44970 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44970, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44970, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44971 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44971, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44971, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44972 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44972, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44972, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96415 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45094 q = 1) (hb : d46864 q = 1) : d355933 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45094, d355933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45094, d355933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105949 (p : Pattern) (ha : d44985 p = 1) (hb : d46864 p = 1) : d355873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44906 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44906, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44984 q = 1) (hb : d46864 q = 1) : d355872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44984, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44984, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44985 q = 1) (hb : d46864 q = 1) : d355873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44985, d355873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44985, d355873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105950 (p : Pattern) (ha : d44992 p = 1) (hb : d46864 p = 1) : d355880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44990 q = 1) (hb : d46864 q = 1) : d355878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44990, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44990, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44991 q = 1) (hb : d46864 q = 1) : d355879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44991, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44991, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44992 q = 1) (hb : d46864 q = 1) : d355880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44992, d355880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44992, d355880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105951 (p : Pattern) (ha : d44998 p = 1) (hb : d46864 p = 1) : d324333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1084 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1084, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d44996 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44881 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44882 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44882, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44882, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44997 q = 1) (hb : d46864 q = 1) : d324332 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44997, d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44997, d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44883 q = 1) (hb : d46864 q = 1) : d46866 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d44883, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44883, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44998 q = 1) (hb : d46864 q = 1) : d324333 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44998, d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44998, d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro105952 (p : Pattern) (ha : d45004 p = 1) (hb : d46864 p = 1) : d374354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d46864 q = 1) : d374349 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105951 q ha hb
    | true =>
      simp only [d44999, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d46864 q = 1) : d374350 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105932 q ha hb
    | true =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d46864 q = 1) : d374351 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44887 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45002 q = 1) (hb : d46864 q = 1) : d374352 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45002, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45003 q = 1) (hb : d46864 q = 1) : d374353 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45003, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44888 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44888, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44888, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44889 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44889, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44889, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45004 q = 1) (hb : d46864 q = 1) : d374354 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45004, d374354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45004, d374354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro105953 (p : Pattern) (ha : d45012 p = 1) (hb : d46864 p = 1) : d355780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44885 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105932 q ha hb
    | true =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44886 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44887 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45010 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45010, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45011 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45011, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45012 q = 1) (hb : d46864 q = 1) : d355780 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45012, d355780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45012, d355780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105954 (p : Pattern) (ha : d45018 p = 1) (hb : d46864 p = 1) : d374360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45005 q = 1) (hb : d46864 q = 1) : d374355 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45005, d374355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105952 q ha hb
    | true =>
      simp only [d45005, d374355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45006 q = 1) (hb : d46864 q = 1) : d374356 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45006, d374356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45006, d374356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45007 q = 1) (hb : d46864 q = 1) : d374357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45007, d374357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45007, d374357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45008 q = 1) (hb : d46864 q = 1) : d374358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45008, d374358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45008, d374358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44891 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105933 q ha hb
    | true =>
      simp only [d44891, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44892 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44892, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44893 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44893, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44893, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44894 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44894, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44894, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45009 q = 1) (hb : d46864 q = 1) : d374359 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45009, d374359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45009, d374359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45013 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105953 q ha hb
    | true =>
      simp only [d45013, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45014 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45014, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45015 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45016 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45016, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45017 q = 1) (hb : d46864 q = 1) : d355785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45017, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45017, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45018 q = 1) (hb : d46864 q = 1) : d374360 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45018, d374360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45018, d374360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105955 (p : Pattern) (ha : d45024 p = 1) (hb : d46864 p = 1) : d374366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45019 q = 1) (hb : d46864 q = 1) : d374361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d374361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105954 q ha hb
    | true =>
      simp only [d45019, d374361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105934 q ha hb
  have h2 (q : Pattern) (ha : d45020 q = 1) (hb : d46864 q = 1) : d374362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d374362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d374362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45021 q = 1) (hb : d46864 q = 1) : d374363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d374363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d374363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44897 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105934 q ha hb
    | true =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h5 (q : Pattern) (ha : d44898 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44899 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45022 q = 1) (hb : d46864 q = 1) : d374364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d374364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45022, d374364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44900 q = 1) (hb : d46864 q = 1) : d355790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44900, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44900, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45023 q = 1) (hb : d46864 q = 1) : d374365 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45023, d374365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45023, d374365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45024 q = 1) (hb : d46864 q = 1) : d374366 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45024, d374366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45024, d374366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105956 (p : Pattern) (ha : d45030 p = 1) (hb : d46864 p = 1) : d374372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45025 q = 1) (hb : d46864 q = 1) : d374367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45025, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105955 q ha hb
    | true =>
      simp only [d45025, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45026 q = 1) (hb : d46864 q = 1) : d374368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45026, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45026, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45027 q = 1) (hb : d46864 q = 1) : d374369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45027, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45027, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45028 q = 1) (hb : d46864 q = 1) : d374370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45028, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45028, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45029 q = 1) (hb : d46864 q = 1) : d374371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45029, d374371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45029, d374371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45030 q = 1) (hb : d46864 q = 1) : d374372 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45030, d374372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45030, d374372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105957 (p : Pattern) (ha : d45065 p = 1) (hb : d46864 p = 1) : d355798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45062 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45062, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45062, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45063 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45063, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45063, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45064 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45064, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45064, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45065 q = 1) (hb : d46864 q = 1) : d355798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45065, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45065, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105958 (p : Pattern) (ha : d46864 p = 1) (hb : d322048 p = 1) : d374378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44986 q = 1) (hb : d46864 q = 1) : d355874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44986, d355874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105949 q ha hb
    | true =>
      simp only [d44986, d355874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96428 q ha hb
  have h2 (q : Pattern) (ha : d44987 q = 1) (hb : d46864 q = 1) : d355875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44987, d355875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44987, d355875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44988 q = 1) (hb : d46864 q = 1) : d355876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44988, d355876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44988, d355876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44989 q = 1) (hb : d46864 q = 1) : d355877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44989, d355877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44989, d355877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44993 q = 1) (hb : d46864 q = 1) : d355881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44993, d355881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105950 q ha hb
    | true =>
      simp only [d44993, d355881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96429 q ha hb
  have h6 (q : Pattern) (ha : d44994 q = 1) (hb : d46864 q = 1) : d355882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44994, d355882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44994, d355882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44995 q = 1) (hb : d46864 q = 1) : d355883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44995, d355883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44995, d355883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45031 q = 1) (hb : d46864 q = 1) : d374373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45031, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105956 q ha hb
    | true =>
      simp only [d45031, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105936 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d322044 q = 1) : d374374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322044, d374374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d322044, d374374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d45066 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45066, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105957 q ha hb
    | true =>
      simp only [d45066, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45067 q = 1) (hb : d46864 q = 1) : d355800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45067, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45067, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d322045 q = 1) : d374375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322045, d374375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322045, d374375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d322046 q = 1) : d374376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322046, d374376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d322046, d374376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d322047 q = 1) : d374377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322047, d374377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322047, d374377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d322048 q = 1) : d374378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322048, d374378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322048, d374378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105959 (p : Pattern) (ha : d45072 p = 1) (hb : d46864 p = 1) : d355916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44906 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44906, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44906, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44984 q = 1) (hb : d46864 q = 1) : d355872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44984, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44984, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45072 q = 1) (hb : d46864 q = 1) : d355916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45072, d355916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45072, d355916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105960 (p : Pattern) (ha : d45077 p = 1) (hb : d46864 p = 1) : d355921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96414 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44905 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44905, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44990 q = 1) (hb : d46864 q = 1) : d355878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44990, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44990, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44991 q = 1) (hb : d46864 q = 1) : d355879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44991, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44991, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45077 q = 1) (hb : d46864 q = 1) : d355921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45077, d355921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45077, d355921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105961 (p : Pattern) (ha : d45081 p = 1) (hb : d46864 p = 1) : d374379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45025 q = 1) (hb : d46864 q = 1) : d374367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45025, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105955 q ha hb
    | true =>
      simp only [d45025, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45026 q = 1) (hb : d46864 q = 1) : d374368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45026, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45026, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45027 q = 1) (hb : d46864 q = 1) : d374369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45027, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45027, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45028 q = 1) (hb : d46864 q = 1) : d374370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45028, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45028, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45029 q = 1) (hb : d46864 q = 1) : d374371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45029, d374371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45029, d374371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45081 q = 1) (hb : d46864 q = 1) : d374379 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45081, d374379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45081, d374379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105962 (p : Pattern) (ha : d45086 p = 1) (hb : d46864 p = 1) : d355805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44903 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105935 q ha hb
    | true =>
      simp only [d44903, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44904 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44904, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45062 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45062, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45062, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45063 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45063, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45063, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45064 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45064, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45064, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45086 q = 1) (hb : d46864 q = 1) : d355805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45086, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45086, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105963 (p : Pattern) (ha : d46864 p = 1) (hb : d322053 p = 1) : d374385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44986 q = 1) (hb : d46864 q = 1) : d355874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44986, d355874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105949 q ha hb
    | true =>
      simp only [d44986, d355874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96428 q ha hb
  have h2 (q : Pattern) (ha : d44987 q = 1) (hb : d46864 q = 1) : d355875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44987, d355875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44987, d355875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44988 q = 1) (hb : d46864 q = 1) : d355876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44988, d355876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44988, d355876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44989 q = 1) (hb : d46864 q = 1) : d355877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44989, d355877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44989, d355877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44993 q = 1) (hb : d46864 q = 1) : d355881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44993, d355881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105950 q ha hb
    | true =>
      simp only [d44993, d355881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96429 q ha hb
  have h6 (q : Pattern) (ha : d44994 q = 1) (hb : d46864 q = 1) : d355882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44994, d355882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44994, d355882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44995 q = 1) (hb : d46864 q = 1) : d355883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44995, d355883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44995, d355883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45031 q = 1) (hb : d46864 q = 1) : d374373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45031, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105956 q ha hb
    | true =>
      simp only [d45031, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105936 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d322044 q = 1) : d374374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322044, d374374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d322044, d374374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d45066 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45066, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105957 q ha hb
    | true =>
      simp only [d45066, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45067 q = 1) (hb : d46864 q = 1) : d355800 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45067, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45067, d355800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d322045 q = 1) : d374375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322045, d374375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322045, d374375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d322046 q = 1) : d374376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322046, d374376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d322046, d374376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d322047 q = 1) : d374377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322047, d374377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322047, d374377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45073 q = 1) (hb : d46864 q = 1) : d355917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45073, d355917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105959 q ha hb
    | true =>
      simp only [d45073, d355917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96436 q ha hb
  have h16 (q : Pattern) (ha : d45074 q = 1) (hb : d46864 q = 1) : d355918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45074, d355918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45074, d355918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45075 q = 1) (hb : d46864 q = 1) : d355919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45075, d355919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45075, d355919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45076 q = 1) (hb : d46864 q = 1) : d355920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45076, d355920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45076, d355920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45078 q = 1) (hb : d46864 q = 1) : d355922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45078, d355922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105960 q ha hb
    | true =>
      simp only [d45078, d355922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96437 q ha hb
  have h20 (q : Pattern) (ha : d45079 q = 1) (hb : d46864 q = 1) : d355923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45079, d355923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45079, d355923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d45080 q = 1) (hb : d46864 q = 1) : d355924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45080, d355924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d45080, d355924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d45082 q = 1) (hb : d46864 q = 1) : d374380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45082, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105961 q ha hb
    | true =>
      simp only [d45082, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105938 q ha hb
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d322049 q = 1) : d374381 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322049, d374381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d322049, d374381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d45087 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45087, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105962 q ha hb
    | true =>
      simp only [d45087, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d45088 q = 1) (hb : d46864 q = 1) : d355807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45088, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d45088, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d46864 q = 1) (hb : d322050 q = 1) : d374382 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322050, d374382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d322050, d374382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d46864 q = 1) (hb : d322051 q = 1) : d374383 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322051, d374383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d322051, d374383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d46864 q = 1) (hb : d322052 q = 1) : d374384 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322052, d374384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d322052, d374384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d46864 q = 1) (hb : d322053 q = 1) : d374385 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322053, d374385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322053, d374385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro105964 (p : Pattern) (ha : d46864 p = 1) (hb : d322060 p = 1) : d374392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45082 q = 1) (hb : d46864 q = 1) : d374380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45082, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105961 q ha hb
    | true =>
      simp only [d45082, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105938 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d322049 q = 1) : d374381 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322049, d374381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322049, d374381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d45087 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45087, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105962 q ha hb
    | true =>
      simp only [d45087, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45088 q = 1) (hb : d46864 q = 1) : d355807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45088, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45088, d355807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d322050 q = 1) : d374382 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322050, d374382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322050, d374382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d322058 q = 1) : d374390 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322058, d374390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322058, d374390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d322059 q = 1) : d374391 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322059, d374391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322059, d374391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d322060 q = 1) : d374392 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322060, d374392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322060, d374392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105965 (p : Pattern) (ha : d45117 p = 1) (hb : d46864 p = 1) : d374403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45107 q = 1) (hb : d46864 q = 1) : d374398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45107, d374398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45107, d374398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105952 q ha hb
  have h2 (q : Pattern) (ha : d45005 q = 1) (hb : d46864 q = 1) : d374355 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45005, d374355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105952 q ha hb
    | true =>
      simp only [d45005, d374355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45108 q = 1) (hb : d46864 q = 1) : d374399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45108, d374399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45108, d374399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45006 q = 1) (hb : d46864 q = 1) : d374356 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45006, d374356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45006, d374356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45109 q = 1) (hb : d46864 q = 1) : d374400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45109, d374400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45109, d374400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45110 q = 1) (hb : d46864 q = 1) : d374401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45110, d374401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45110, d374401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44934 q = 1) (hb : d46864 q = 1) : d355822 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44934, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44934, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105933 q ha hb
  have h8 (q : Pattern) (ha : d44891 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44891, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105933 q ha hb
    | true =>
      simp only [d44891, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44935 q = 1) (hb : d46864 q = 1) : d355823 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44935, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44935, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44892 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44892, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44892, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44936 q = 1) (hb : d46864 q = 1) : d355824 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44936, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44936, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44937 q = 1) (hb : d46864 q = 1) : d355825 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44937, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44937, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45111 q = 1) (hb : d46864 q = 1) : d374402 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45111, d374402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45111, d374402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45112 q = 1) (hb : d46864 q = 1) : d355822 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45112, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45112, d355822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105953 q ha hb
  have h15 (q : Pattern) (ha : d45013 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105953 q ha hb
    | true =>
      simp only [d45013, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45113 q = 1) (hb : d46864 q = 1) : d355823 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45113, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45113, d355823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45014 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45014, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45114 q = 1) (hb : d46864 q = 1) : d355824 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45114, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45114, d355824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45115 q = 1) (hb : d46864 q = 1) : d355825 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45115, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d45115, d355825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d45116 q = 1) (hb : d46864 q = 1) : d355826 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45116, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d45116, d355826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d45117 q = 1) (hb : d46864 q = 1) : d374403 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45117, d374403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45117, d374403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro105966 (p : Pattern) (ha : d45123 p = 1) (hb : d46864 p = 1) : d374409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45118 q = 1) (hb : d46864 q = 1) : d374404 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45118, d374404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105965 q ha hb
    | true =>
      simp only [d45118, d374404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105941 q ha hb
  have h2 (q : Pattern) (ha : d45119 q = 1) (hb : d46864 q = 1) : d374405 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45119, d374405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45119, d374405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45120 q = 1) (hb : d46864 q = 1) : d374406 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45120, d374406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45120, d374406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44940 q = 1) (hb : d46864 q = 1) : d355828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105941 q ha hb
    | true =>
      simp only [d44940, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
  have h5 (q : Pattern) (ha : d44941 q = 1) (hb : d46864 q = 1) : d355829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44942 q = 1) (hb : d46864 q = 1) : d355830 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45121 q = 1) (hb : d46864 q = 1) : d374407 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45121, d374407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45121, d374407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44943 q = 1) (hb : d46864 q = 1) : d355831 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44943, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44943, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45122 q = 1) (hb : d46864 q = 1) : d374408 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45122, d374408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45122, d374408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45123 q = 1) (hb : d46864 q = 1) : d374409 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45123, d374409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45123, d374409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro105967 (p : Pattern) (ha : d45129 p = 1) (hb : d46864 p = 1) : d374415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45124 q = 1) (hb : d46864 q = 1) : d374410 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45124, d374410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105966 q ha hb
    | true =>
      simp only [d45124, d374410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45125 q = 1) (hb : d46864 q = 1) : d374411 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45125, d374411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45125, d374411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44946 q = 1) (hb : d46864 q = 1) : d355834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105942 q ha hb
    | true =>
      simp only [d44946, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44947 q = 1) (hb : d46864 q = 1) : d355835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45126 q = 1) (hb : d46864 q = 1) : d374412 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45126, d374412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45126, d374412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45127 q = 1) (hb : d46864 q = 1) : d374413 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45127, d374413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45127, d374413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45128 q = 1) (hb : d46864 q = 1) : d374414 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45128, d374414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45128, d374414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45129 q = 1) (hb : d46864 q = 1) : d374415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45129, d374415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45129, d374415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105968 (p : Pattern) (ha : d45154 p = 1) (hb : d46864 p = 1) : d355839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44946 q = 1) (hb : d46864 q = 1) : d355834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44946, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105942 q ha hb
    | true =>
      simp only [d44946, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44947 q = 1) (hb : d46864 q = 1) : d355835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44947, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44947, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45151 q = 1) (hb : d46864 q = 1) : d355836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45151, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45151, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45152 q = 1) (hb : d46864 q = 1) : d355837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45152, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45152, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45153 q = 1) (hb : d46864 q = 1) : d355838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45153, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45153, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45154 q = 1) (hb : d46864 q = 1) : d355839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45154, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45154, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105969 (p : Pattern) (ha : d46864 p = 1) (hb : d322070 p = 1) : d374421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45130 q = 1) (hb : d46864 q = 1) : d374416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45130, d374416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105967 q ha hb
    | true =>
      simp only [d45130, d374416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105943 q ha hb
  have h2 (q : Pattern) (ha : d46864 q = 1) (hb : d322066 q = 1) : d374417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d322066, d374417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d322066, d374417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d45155 q = 1) (hb : d46864 q = 1) : d355840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45155, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105968 q ha hb
    | true =>
      simp only [d45155, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45156 q = 1) (hb : d46864 q = 1) : d355841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45156, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45156, d355841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d322067 q = 1) : d374418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d322067, d374418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322067, d374418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d322068 q = 1) : d374419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d322068, d374419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322068, d374419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d322069 q = 1) : d374420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d322069, d374420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322069, d374420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d322070 q = 1) : d374421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d322070, d374421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322070, d374421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105970 (p : Pattern) (ha : d46864 p = 1) (hb : d322076 p = 1) : d374427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44974 q = 1) (hb : d46864 q = 1) : d355862 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44974, d355862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44974, d355862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105946 q ha hb
  have h2 (q : Pattern) (ha : d44975 q = 1) (hb : d46864 q = 1) : d355863 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44975, d355863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44975, d355863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44981 q = 1) (hb : d46864 q = 1) : d355869 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44981, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105946 q ha hb
    | true =>
      simp only [d44981, d355869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105947 q ha hb
  have h4 (q : Pattern) (ha : d44982 q = 1) (hb : d46864 q = 1) : d355870 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44982, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44982, d355870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44983 q = 1) (hb : d46864 q = 1) : d355871 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44983, d355871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44983, d355871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d322054 q = 1) : d374386 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322054, d374386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105958 q ha hb
    | true =>
      simp only [d322054, d374386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105963 q ha hb
  have h7 (q : Pattern) (ha : d45095 q = 1) (hb : d46864 q = 1) : d355934 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d45095, d355934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105948 q ha hb
    | true =>
      simp only [d45095, d355934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96426 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d322055 q = 1) : d374387 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322055, d374387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322055, d374387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d322056 q = 1) : d374388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322056, d374388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d322056, d374388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d322057 q = 1) : d374389 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322057, d374389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d322057, d374389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d322061 q = 1) : d374393 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322061, d374393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322061, d374393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105964 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96446 q ha hb
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d322062 q = 1) : d374394 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322062, d374394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d322062, d374394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d322063 q = 1) : d374395 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322063, d374395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d322063, d374395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d322064 q = 1) : d374396 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322064, d374396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d322064, d374396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d46864 q = 1) (hb : d322065 q = 1) : d374397 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322065, d374397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d322065, d374397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46864 q = 1) (hb : d322071 q = 1) : d374422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d322071, d374422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322071, d374422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105969 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96447 q ha hb
  have h19 (q : Pattern) (ha : d46864 q = 1) (hb : d322072 q = 1) : d374423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d322072, d374423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d322072, d374423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d46864 q = 1) (hb : d322073 q = 1) : d374424 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d322073, d374424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d322073, d374424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d46864 q = 1) (hb : d322074 q = 1) : d374425 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d322074, d374425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d322074, d374425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d46864 q = 1) (hb : d322075 q = 1) : d374426 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d322075, d374426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d322075, d374426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d46864 q = 1) (hb : d322076 q = 1) : d374427 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d322076, d374427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d322076, d374427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro105971 (p : Pattern) (ha : d46864 p = 1) (hb : d322082 p = 1) : d374433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96424 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d46864 q = 1) (hb : d322039 q = 1) : d355852 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322039, d355852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322039, d355852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105945 q ha hb
  have h6 (q : Pattern) (ha : d46864 q = 1) (hb : d322040 q = 1) : d355853 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322040, d355853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322040, d355853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46864 q = 1) (hb : d322041 q = 1) : d355854 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322041, d355854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322041, d355854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46864 q = 1) (hb : d322042 q = 1) : d355855 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322042, d355855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322042, d355855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46864 q = 1) (hb : d322043 q = 1) : d355856 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322043, d355856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d322043, d355856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46864 q = 1) (hb : d322077 q = 1) : d374428 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d322077, d374428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322077, d374428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105970 q ha hb
  have h11 (q : Pattern) (ha : d46864 q = 1) (hb : d322078 q = 1) : d374429 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d322078, d374429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322078, d374429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d46864 q = 1) (hb : d322079 q = 1) : d374430 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d322079, d374430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322079, d374430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d46864 q = 1) (hb : d322080 q = 1) : d374431 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d322080, d374431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322080, d374431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d46864 q = 1) (hb : d322081 q = 1) : d374432 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d322081, d374432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322081, d374432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d46864 q = 1) (hb : d322082 q = 1) : d374433 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322082, d374433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d322082, d374433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro105972 (p : Pattern) (ha : d45175 p = 1) (hb : d46864 p = 1) : d374366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45019 q = 1) (hb : d46864 q = 1) : d374361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d374361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105954 q ha hb
    | true =>
      simp only [d45019, d374361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105934 q ha hb
  have h2 (q : Pattern) (ha : d45020 q = 1) (hb : d46864 q = 1) : d374362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d374362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d374362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45021 q = 1) (hb : d46864 q = 1) : d374363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d374363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d374363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44897 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105934 q ha hb
    | true =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h5 (q : Pattern) (ha : d44898 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44899 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45022 q = 1) (hb : d46864 q = 1) : d374364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d374364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45022, d374364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45173 q = 1) (hb : d46864 q = 1) : d355790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45173, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45173, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45174 q = 1) (hb : d46864 q = 1) : d374365 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45174, d374365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45174, d374365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45175 q = 1) (hb : d46864 q = 1) : d374366 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45175, d374366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45175, d374366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro105973 (p : Pattern) (ha : d45179 p = 1) (hb : d46864 p = 1) : d355792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44897 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105934 q ha hb
    | true =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h2 (q : Pattern) (ha : d44898 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44899 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45173 q = 1) (hb : d46864 q = 1) : d355790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45173, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45173, d355790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45178 q = 1) (hb : d46864 q = 1) : d355791 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45178, d355791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45178, d355791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45179 q = 1) (hb : d46864 q = 1) : d355792 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45179, d355792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45179, d355792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105974 (p : Pattern) (ha : d45185 p = 1) (hb : d46864 p = 1) : d374372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d46864 q = 1) : d374367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105972 q ha hb
    | true =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d46864 q = 1) : d374368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105973 q ha hb
    | true =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d46864 q = 1) : d374369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d46864 q = 1) : d374370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45184 q = 1) (hb : d46864 q = 1) : d374371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45184, d374371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45184, d374371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45185 q = 1) (hb : d46864 q = 1) : d374372 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45185, d374372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45185, d374372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105975 (p : Pattern) (ha : d45189 p = 1) (hb : d46864 p = 1) : d355798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105973 q ha hb
    | true =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45188 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45188, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45188, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45189 q = 1) (hb : d46864 q = 1) : d355798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45189, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45189, d355798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105976 (p : Pattern) (ha : d45195 p = 1) (hb : d46864 p = 1) : d374438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d46864 q = 1) : d374373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105974 q ha hb
    | true =>
      simp only [d45190, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105975 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d46864 q = 1) : d374434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d46864 q = 1) : d374435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d46864 q = 1) : d374436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d46864 q = 1) : d374437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45195 q = 1) (hb : d46864 q = 1) : d374438 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45195, d374438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45195, d374438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105977 (p : Pattern) (ha : d45198 p = 1) (hb : d46864 p = 1) : d374379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d46864 q = 1) : d374367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105972 q ha hb
    | true =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d46864 q = 1) : d374368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105973 q ha hb
    | true =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d46864 q = 1) : d374369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d46864 q = 1) : d374370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45184 q = 1) (hb : d46864 q = 1) : d374371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45184, d374371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45184, d374371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45198 q = 1) (hb : d46864 q = 1) : d374379 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45198, d374379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45198, d374379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro105978 (p : Pattern) (ha : d45199 p = 1) (hb : d46864 p = 1) : d355805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105973 q ha hb
    | true =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45188 q = 1) (hb : d46864 q = 1) : d355797 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45188, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45188, d355797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45199 q = 1) (hb : d46864 q = 1) : d355805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45199, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45199, d355805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105979 (p : Pattern) (ha : d45205 p = 1) (hb : d46864 p = 1) : d374445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d46864 q = 1) : d374373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105974 q ha hb
    | true =>
      simp only [d45190, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105975 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d46864 q = 1) : d374434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d46864 q = 1) : d374435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d46864 q = 1) : d374436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d46864 q = 1) : d374437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45200 q = 1) (hb : d46864 q = 1) : d374380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45200, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105977 q ha hb
    | true =>
      simp only [d45200, d374380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105978 q ha hb
  have h7 (q : Pattern) (ha : d45201 q = 1) (hb : d46864 q = 1) : d374441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45201, d374441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45201, d374441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45202 q = 1) (hb : d46864 q = 1) : d374442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45202, d374442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45202, d374442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45203 q = 1) (hb : d46864 q = 1) : d374443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45203, d374443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45203, d374443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45204 q = 1) (hb : d46864 q = 1) : d374444 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45204, d374444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45204, d374444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45205 q = 1) (hb : d46864 q = 1) : d374445 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45205, d374445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45205, d374445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105980 (p : Pattern) (ha : d45363 p = 1) (hb : d46864 p = 1) : d374526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45190 q = 1) (hb : d46864 q = 1) : d374373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45190, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105974 q ha hb
    | true =>
      simp only [d45190, d374373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105975 q ha hb
  have h2 (q : Pattern) (ha : d45191 q = 1) (hb : d46864 q = 1) : d374434 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45191, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45191, d374434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45192 q = 1) (hb : d46864 q = 1) : d374435 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45192, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45192, d374435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45193 q = 1) (hb : d46864 q = 1) : d374436 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45193, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45193, d374436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45194 q = 1) (hb : d46864 q = 1) : d374437 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45194, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45194, d374437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45358 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45358, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105975 q ha hb
    | true =>
      simp only [d45358, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45359 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45359, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45359, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45360 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45360, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45360, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45361 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45361, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45361, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45362 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45362, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45362, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45363 q = 1) (hb : d46864 q = 1) : d374526 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45363, d374526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45363, d374526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105981 (p : Pattern) (ha : d45369 p = 1) (hb : d46864 p = 1) : d355868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45358 q = 1) (hb : d46864 q = 1) : d355799 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45358, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105975 q ha hb
    | true =>
      simp only [d45358, d355799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45359 q = 1) (hb : d46864 q = 1) : d355857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45359, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45359, d355857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45360 q = 1) (hb : d46864 q = 1) : d355858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45360, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45360, d355858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45361 q = 1) (hb : d46864 q = 1) : d355859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45361, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45361, d355859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45362 q = 1) (hb : d46864 q = 1) : d355860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45362, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45362, d355860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45364 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45364, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105978 q ha hb
    | true =>
      simp only [d45364, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45365 q = 1) (hb : d46864 q = 1) : d355864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45365, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45365, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45366 q = 1) (hb : d46864 q = 1) : d355865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45366, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45366, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45367 q = 1) (hb : d46864 q = 1) : d355866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45367, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45367, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45368 q = 1) (hb : d46864 q = 1) : d355867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45368, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45368, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45369 q = 1) (hb : d46864 q = 1) : d355868 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45369, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45369, d355868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105982 (p : Pattern) (ha : d45378 p = 1) (hb : d46864 p = 1) : d356088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45364 q = 1) (hb : d46864 q = 1) : d355806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45364, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105978 q ha hb
    | true =>
      simp only [d45364, d355806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45365 q = 1) (hb : d46864 q = 1) : d355864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45365, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45365, d355864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45366 q = 1) (hb : d46864 q = 1) : d355865 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45366, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45366, d355865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45367 q = 1) (hb : d46864 q = 1) : d355866 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45367, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45367, d355866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45368 q = 1) (hb : d46864 q = 1) : d355867 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45368, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45368, d355867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45378 q = 1) (hb : d46864 q = 1) : d356088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45378, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45378, d356088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105983 (p : Pattern) (ha : d45421 p = 1) (hb : d46864 p = 1) : d355833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44940 q = 1) (hb : d46864 q = 1) : d355828 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44940, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105941 q ha hb
    | true =>
      simp only [d44940, d355828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96420 q ha hb
  have h2 (q : Pattern) (ha : d44941 q = 1) (hb : d46864 q = 1) : d355829 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44941, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44941, d355829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44942 q = 1) (hb : d46864 q = 1) : d355830 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44942, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44942, d355830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45411 q = 1) (hb : d46864 q = 1) : d355831 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45411, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45411, d355831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45420 q = 1) (hb : d46864 q = 1) : d355832 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45420, d355832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45420, d355832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45421 q = 1) (hb : d46864 q = 1) : d355833 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45421, d355833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45421, d355833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105984 (p : Pattern) (ha : d45477 p = 1) (hb : d46864 p = 1) : d355839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45422 q = 1) (hb : d46864 q = 1) : d355834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45422, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105983 q ha hb
    | true =>
      simp only [d45422, d355834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45423 q = 1) (hb : d46864 q = 1) : d355835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45423, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45423, d355835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45474 q = 1) (hb : d46864 q = 1) : d355836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45474, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45474, d355836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45475 q = 1) (hb : d46864 q = 1) : d355837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45475, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45475, d355837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45476 q = 1) (hb : d46864 q = 1) : d355838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45476, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45476, d355838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45477 q = 1) (hb : d46864 q = 1) : d355839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45477, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45477, d355839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro105985 (p : Pattern) (ha : d45483 p = 1) (hb : d46864 p = 1) : d356134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45478 q = 1) (hb : d46864 q = 1) : d355840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d45478, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105984 q ha hb
    | true =>
      simp only [d45478, d355840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45479 q = 1) (hb : d46864 q = 1) : d356130 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d45479, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45479, d356130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45480 q = 1) (hb : d46864 q = 1) : d356131 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45480, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45480, d356131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45481 q = 1) (hb : d46864 q = 1) : d356132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d45481, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45481, d356132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45482 q = 1) (hb : d46864 q = 1) : d356133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d45482, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45482, d356133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45483 q = 1) (hb : d46864 q = 1) : d356134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d45483, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45483, d356134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105986 (p : Pattern) (ha : d45210 p = 1) (hb : d46864 p = 1) : d374450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d46864 q = 1) : d374367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105972 q ha hb
    | true =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d46864 q = 1) : d374368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105973 q ha hb
    | true =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d46864 q = 1) : d374369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45183 q = 1) (hb : d46864 q = 1) : d374370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45183, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45183, d374370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45209 q = 1) (hb : d46864 q = 1) : d374449 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45209, d374449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45209, d374449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45210 q = 1) (hb : d46864 q = 1) : d374450 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45210, d374450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45210, d374450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105987 (p : Pattern) (ha : d45212 p = 1) (hb : d46864 p = 1) : d355873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105973 q ha hb
    | true =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45187 q = 1) (hb : d46864 q = 1) : d355796 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45187, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45187, d355796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45211 q = 1) (hb : d46864 q = 1) : d355872 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45211, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45211, d355872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45212 q = 1) (hb : d46864 q = 1) : d355873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45212, d355873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45212, d355873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105988 (p : Pattern) (ha : d45219 p = 1) (hb : d46864 p = 1) : d374457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d46864 q = 1) : d374367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105972 q ha hb
    | true =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d46864 q = 1) : d374368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45180 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105973 q ha hb
    | true =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45181 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45182 q = 1) (hb : d46864 q = 1) : d374369 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45182, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45182, d374369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45217 q = 1) (hb : d46864 q = 1) : d374455 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45217, d374455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45217, d374455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45218 q = 1) (hb : d46864 q = 1) : d374456 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45218, d374456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45218, d374456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45219 q = 1) (hb : d46864 q = 1) : d374457 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45219, d374457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45219, d374457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105989 (p : Pattern) (ha : d45222 p = 1) (hb : d46864 p = 1) : d355880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45180 q = 1) (hb : d46864 q = 1) : d355793 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105973 q ha hb
    | true =>
      simp only [d45180, d355793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45181 q = 1) (hb : d46864 q = 1) : d355794 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45181, d355794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45186 q = 1) (hb : d46864 q = 1) : d355795 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45186, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45186, d355795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45220 q = 1) (hb : d46864 q = 1) : d355878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45220, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45220, d355878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45221 q = 1) (hb : d46864 q = 1) : d355879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45221, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45221, d355879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45222 q = 1) (hb : d46864 q = 1) : d355880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45222, d355880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45222, d355880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro105990 (p : Pattern) (ha : d45227 p = 1) (hb : d46864 p = 1) : d374461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44881 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44882 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44882, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44882, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45226 q = 1) (hb : d46864 q = 1) : d324332 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45226, d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45226, d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45227 q = 1) (hb : d46864 q = 1) : d374461 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45227, d374461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45227, d374461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105991 (p : Pattern) (ha : d45234 p = 1) (hb : d46864 p = 1) : d324333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1084 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1084, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d44996 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44881 q = 1) (hb : d46864 q = 1) : d46864 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d45231 q = 1) (hb : d46864 q = 1) : d46865 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45231, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45231, d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45232 q = 1) (hb : d46864 q = 1) : d324332 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45232, d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45232, d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d14, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15, d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45233 q = 1) (hb : d46864 q = 1) : d46866 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d45233, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45233, d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45234 q = 1) (hb : d46864 q = 1) : d324333 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d45234, d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45234, d324333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro105992 (p : Pattern) (ha : d45240 p = 1) (hb : d46864 p = 1) : d374467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45228 q = 1) (hb : d46864 q = 1) : d374462 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45228, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105990 q ha hb
    | true =>
      simp only [d45228, d374462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45229 q = 1) (hb : d46864 q = 1) : d374463 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45229, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45229, d374463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44999 q = 1) (hb : d46864 q = 1) : d374349 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105951 q ha hb
    | true =>
      simp only [d44999, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45000 q = 1) (hb : d46864 q = 1) : d374350 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45000, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45230 q = 1) (hb : d46864 q = 1) : d374464 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45230, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45230, d374464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45235 q = 1) (hb : d46864 q = 1) : d374349 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d45235, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105991 q ha hb
    | true =>
      simp only [d45235, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45236 q = 1) (hb : d46864 q = 1) : d374350 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45236, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45236, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44885 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105932 q ha hb
    | true =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44886 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d45237 q = 1) (hb : d46864 q = 1) : d374351 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45237, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45237, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45238 q = 1) (hb : d46864 q = 1) : d374465 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45238, d374465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45238, d374465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d45239 q = 1) (hb : d46864 q = 1) : d374466 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45239, d374466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45239, d374466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45001 q = 1) (hb : d46864 q = 1) : d374351 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45001, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d44887 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45002 q = 1) (hb : d46864 q = 1) : d374352 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45002, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d45003 q = 1) (hb : d46864 q = 1) : d374353 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d45003, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d45240 q = 1) (hb : d46864 q = 1) : d374467 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45240, d374467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45240, d374467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105993 (p : Pattern) (ha : d45245 p = 1) (hb : d46864 p = 1) : d374354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d46864 q = 1) : d374349 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105951 q ha hb
    | true =>
      simp only [d44999, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d46864 q = 1) : d374350 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105932 q ha hb
    | true =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d46864 q = 1) : d374351 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44887 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d45002 q = 1) (hb : d46864 q = 1) : d374352 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45002, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45002, d374352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45003 q = 1) (hb : d46864 q = 1) : d374353 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45003, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45003, d374353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45010 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d45010, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45011 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45011, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45245 q = 1) (hb : d46864 q = 1) : d374354 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45245, d374354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45245, d374354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro105994 (p : Pattern) (ha : d45253 p = 1) (hb : d46864 p = 1) : d374475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44999 q = 1) (hb : d46864 q = 1) : d374349 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44999, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105951 q ha hb
    | true =>
      simp only [d44999, d374349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45000 q = 1) (hb : d46864 q = 1) : d374350 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d45000, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45000, d374350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44885 q = 1) (hb : d46864 q = 1) : d46871 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105932 q ha hb
    | true =>
      simp only [d44885, d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44886 q = 1) (hb : d46864 q = 1) : d355776 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44886, d355776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45001 q = 1) (hb : d46864 q = 1) : d374351 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d45001, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45001, d374351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45251 q = 1) (hb : d46864 q = 1) : d374473 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45251, d374473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45251, d374473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45252 q = 1) (hb : d46864 q = 1) : d374474 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45252, d374474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45252, d374474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96411 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44887 q = 1) (hb : d46864 q = 1) : d355777 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44887, d355777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d45010 q = 1) (hb : d46864 q = 1) : d355778 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d45010, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45010, d355778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45011 q = 1) (hb : d46864 q = 1) : d355779 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d45011, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d45011, d355779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d45253 q = 1) (hb : d46864 q = 1) : d374475 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d45253, d374475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45253, d374475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro105995 (p : Pattern) (ha : d45259 p = 1) (hb : d46864 p = 1) : d374481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45241 q = 1) (hb : d46864 q = 1) : d374468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45241, d374468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105992 q ha hb
    | true =>
      simp only [d45241, d374468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45242 q = 1) (hb : d46864 q = 1) : d374469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45242, d374469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45242, d374469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45243 q = 1) (hb : d46864 q = 1) : d374470 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45243, d374470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45243, d374470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45244 q = 1) (hb : d46864 q = 1) : d374471 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45244, d374471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45244, d374471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45246 q = 1) (hb : d46864 q = 1) : d374355 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45246, d374355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105993 q ha hb
    | true =>
      simp only [d45246, d374355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45247 q = 1) (hb : d46864 q = 1) : d374356 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45247, d374356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45247, d374356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45248 q = 1) (hb : d46864 q = 1) : d374357 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45248, d374357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45248, d374357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45249 q = 1) (hb : d46864 q = 1) : d374358 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45249, d374358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45249, d374358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45250 q = 1) (hb : d46864 q = 1) : d374472 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45250, d374472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45250, d374472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45254 q = 1) (hb : d46864 q = 1) : d374476 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45254, d374476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105994 q ha hb
    | true =>
      simp only [d45254, d374476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45255 q = 1) (hb : d46864 q = 1) : d374477 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45255, d374477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45255, d374477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d45256 q = 1) (hb : d46864 q = 1) : d374478 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45256, d374478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45256, d374478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d45257 q = 1) (hb : d46864 q = 1) : d374479 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45257, d374479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d45257, d374479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d45013 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105953 q ha hb
    | true =>
      simp only [d45013, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d45014 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d45014, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d45015 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d45016 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d45016, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d45258 q = 1) (hb : d46864 q = 1) : d374480 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45258, d374480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d45258, d374480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d45259 q = 1) (hb : d46864 q = 1) : d374481 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45259, d374481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45259, d374481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro105996 (p : Pattern) (ha : d45263 p = 1) (hb : d46864 p = 1) : d355786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45013 q = 1) (hb : d46864 q = 1) : d355781 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d45013, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105953 q ha hb
    | true =>
      simp only [d45013, d355781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45014 q = 1) (hb : d46864 q = 1) : d355782 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d45014, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d45014, d355782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45015 q = 1) (hb : d46864 q = 1) : d355783 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d45015, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45015, d355783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45016 q = 1) (hb : d46864 q = 1) : d355784 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d45016, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45016, d355784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96412 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d45017 q = 1) (hb : d46864 q = 1) : d355785 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d45017, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45017, d355785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d45263 q = 1) (hb : d46864 q = 1) : d355786 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d45263, d355786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d45263, d355786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro105997 (p : Pattern) (ha : d45269 p = 1) (hb : d46864 p = 1) : d374487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45260 q = 1) (hb : d46864 q = 1) : d374482 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45260, d374482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105995 q ha hb
    | true =>
      simp only [d45260, d374482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105954 q ha hb
  have h2 (q : Pattern) (ha : d45261 q = 1) (hb : d46864 q = 1) : d374483 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45261, d374483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45261, d374483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45262 q = 1) (hb : d46864 q = 1) : d374484 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45262, d374484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45262, d374484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d45264 q = 1) (hb : d46864 q = 1) : d374361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45264, d374361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105954 q ha hb
    | true =>
      simp only [d45264, d374361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105996 q ha hb
  have h5 (q : Pattern) (ha : d45265 q = 1) (hb : d46864 q = 1) : d374362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45265, d374362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45265, d374362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45266 q = 1) (hb : d46864 q = 1) : d374363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45266, d374363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45266, d374363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d45267 q = 1) (hb : d46864 q = 1) : d374485 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45267, d374485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45267, d374485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d45019 q = 1) (hb : d46864 q = 1) : d374361 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d45019, d374361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105954 q ha hb
    | true =>
      simp only [d45019, d374361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105934 q ha hb
  have h9 (q : Pattern) (ha : d45020 q = 1) (hb : d46864 q = 1) : d374362 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d45020, d374362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45020, d374362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d45021 q = 1) (hb : d46864 q = 1) : d374363 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d45021, d374363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45021, d374363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44897 q = 1) (hb : d46864 q = 1) : d355787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105934 q ha hb
    | true =>
      simp only [d44897, d355787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96413 q ha hb
  have h12 (q : Pattern) (ha : d44898 q = 1) (hb : d46864 q = 1) : d355788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44898, d355788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44899 q = 1) (hb : d46864 q = 1) : d355789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44899, d355789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d45022 q = 1) (hb : d46864 q = 1) : d374364 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d45022, d374364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d45022, d374364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d45268 q = 1) (hb : d46864 q = 1) : d374486 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d45268, d374486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d45268, d374486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d45269 q = 1) (hb : d46864 q = 1) : d374487 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d45269, d374487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d45269, d374487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro105998 (p : Pattern) (ha : d45275 p = 1) (hb : d46864 p = 1) : d374493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45270 q = 1) (hb : d46864 q = 1) : d374488 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45270, d374488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105997 q ha hb
    | true =>
      simp only [d45270, d374488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45271 q = 1) (hb : d46864 q = 1) : d374489 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45271, d374489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45271, d374489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45176 q = 1) (hb : d46864 q = 1) : d374367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105972 q ha hb
    | true =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45177 q = 1) (hb : d46864 q = 1) : d374368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d45272 q = 1) (hb : d46864 q = 1) : d374490 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45272, d374490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45272, d374490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d45273 q = 1) (hb : d46864 q = 1) : d374491 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45273, d374491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d45273, d374491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d45274 q = 1) (hb : d46864 q = 1) : d374492 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45274, d374492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d45274, d374492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d45275 q = 1) (hb : d46864 q = 1) : d374493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45275, d374493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45275, d374493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro105999 (p : Pattern) (ha : d45326 p = 1) (hb : d46864 p = 1) : d374499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d45176 q = 1) (hb : d46864 q = 1) : d374367 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105972 q ha hb
    | true =>
      simp only [d45176, d374367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d45177 q = 1) (hb : d46864 q = 1) : d374368 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45177, d374368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d45323 q = 1) (hb : d46864 q = 1) : d374496 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d45323, d374496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45323, d374496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d45324 q = 1) (hb : d46864 q = 1) : d374497 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d45324, d374497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d45324, d374497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d45325 q = 1) (hb : d46864 q = 1) : d374498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d45325, d374498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d45325, d374498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d45326 q = 1) (hb : d46864 q = 1) : d374499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d45326, d374499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d45326, d374499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
