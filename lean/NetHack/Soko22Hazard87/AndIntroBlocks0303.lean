import NetHack.Soko22Hazard87.AndIntroBlocks0302
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro75750 (p : Pattern) (ha : d292627 p = 1) (hb : d293771 p = 1) : d294930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292521 q = 1) (hb : d293657 q = 1) : d294834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292521, d293657, d294834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75723 q ha hb
    | true =>
      simp only [d292521, d293657, d294834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75724 q ha hb
  have h2 (q : Pattern) (ha : d292522 q = 1) (hb : d293658 q = 1) : d294835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292522, d293658, d294835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292522, d293658, d294835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292523 q = 1) (hb : d293659 q = 1) : d294836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292523, d293659, d294836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292523, d293659, d294836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292524 q = 1) (hb : d293660 q = 1) : d294837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292524, d293660, d294837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292524, d293660, d294837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292525 q = 1) (hb : d293661 q = 1) : d294838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292525, d293661, d294838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292525, d293661, d294838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292622 q = 1) (hb : d293766 q = 1) : d294925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292622, d293766, d294925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75724 q ha hb
    | true =>
      simp only [d292622, d293766, d294925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292623 q = 1) (hb : d293767 q = 1) : d294926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292623, d293767, d294926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292623, d293767, d294926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292624 q = 1) (hb : d293768 q = 1) : d294927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292624, d293768, d294927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292624, d293768, d294927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292625 q = 1) (hb : d293769 q = 1) : d294928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292625, d293769, d294928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292625, d293769, d294928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292626 q = 1) (hb : d293770 q = 1) : d294929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292626, d293770, d294929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292626, d293770, d294929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292627 q = 1) (hb : d293771 q = 1) : d294930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292627, d293771, d294930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292627, d293771, d294930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75751 (p : Pattern) (ha : d292633 p = 1) (hb : d293777 p = 1) : d294936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292622 q = 1) (hb : d293766 q = 1) : d294925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292622, d293766, d294925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75724 q ha hb
    | true =>
      simp only [d292622, d293766, d294925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292623 q = 1) (hb : d293767 q = 1) : d294926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292623, d293767, d294926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292623, d293767, d294926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292624 q = 1) (hb : d293768 q = 1) : d294927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292624, d293768, d294927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292624, d293768, d294927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292625 q = 1) (hb : d293769 q = 1) : d294928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292625, d293769, d294928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292625, d293769, d294928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292626 q = 1) (hb : d293770 q = 1) : d294929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292626, d293770, d294929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292626, d293770, d294929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292628 q = 1) (hb : d293772 q = 1) : d294931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292628, d293772, d294931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75727 q ha hb
    | true =>
      simp only [d292628, d293772, d294931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292629 q = 1) (hb : d293773 q = 1) : d294932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292629, d293773, d294932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292629, d293773, d294932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292630 q = 1) (hb : d293774 q = 1) : d294933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292630, d293774, d294933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292630, d293774, d294933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292631 q = 1) (hb : d293775 q = 1) : d294934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292631, d293775, d294934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292631, d293775, d294934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292632 q = 1) (hb : d293776 q = 1) : d294935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292632, d293776, d294935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292632, d293776, d294935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292633 q = 1) (hb : d293777 q = 1) : d294936 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292633, d293777, d294936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292633, d293777, d294936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75752 (p : Pattern) (ha : d292640 p = 1) (hb : d293784 p = 1) : d294943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292612 q = 1) (hb : d293756 q = 1) : d294915 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292612, d293756, d294915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75747 q ha hb
    | true =>
      simp only [d292612, d293756, d294915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75726 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292531 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292613 q = 1) (hb : d293757 q = 1) : d294916 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292613, d293757, d294916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292613, d293757, d294916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d292615 q = 1) (hb : d293759 q = 1) : d294918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292615, d293759, d294918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75748 q ha hb
    | true =>
      simp only [d292615, d293759, d294918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292616 q = 1) (hb : d293760 q = 1) : d294919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292616, d293760, d294919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292616, d293760, d294919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292617 q = 1) (hb : d293761 q = 1) : d294920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292617, d293761, d294920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292617, d293761, d294920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292638 q = 1) (hb : d293782 q = 1) : d294941 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292638, d293782, d294941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292638, d293782, d294941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292639 q = 1) (hb : d293783 q = 1) : d294942 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292639, d293783, d294942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292639, d293783, d294942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292640 q = 1) (hb : d293784 q = 1) : d294943 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292640, d293784, d294943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292640, d293784, d294943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro75753 (p : Pattern) (ha : d292642 p = 1) (hb : d293786 p = 1) : d294945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292628 q = 1) (hb : d293772 q = 1) : d294931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292628, d293772, d294931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75727 q ha hb
    | true =>
      simp only [d292628, d293772, d294931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292629 q = 1) (hb : d293773 q = 1) : d294932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292629, d293773, d294932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292629, d293773, d294932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292630 q = 1) (hb : d293774 q = 1) : d294933 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292630, d293774, d294933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292630, d293774, d294933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292631 q = 1) (hb : d293775 q = 1) : d294934 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292631, d293775, d294934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292631, d293775, d294934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292632 q = 1) (hb : d293776 q = 1) : d294935 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292632, d293776, d294935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292632, d293776, d294935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292642 q = 1) (hb : d293786 q = 1) : d294945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292642, d293786, d294945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292642, d293786, d294945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75754 (p : Pattern) (ha : d206754 p = 1) (hb : d292692 p = 1) : d294967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d206721 q = 1) (hb : d292668 q = 1) : d293415 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d206721, d292668, d293415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206721, d292668, d293415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75713 q ha hb
  have h2 (q : Pattern) (ha : d206497 q = 1) (hb : d292481 q = 1) : d293372 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d206497, d292481, d293372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75713 q ha hb
    | true =>
      simp only [d206497, d292481, d293372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d206722 q = 1) (hb : d292669 q = 1) : d293416 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d206722, d292669, d293416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206722, d292669, d293416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d206498 q = 1) (hb : d292482 q = 1) : d293373 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d206498, d292482, d293373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206498, d292482, d293373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d206723 q = 1) (hb : d292670 q = 1) : d293417 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d206723, d292670, d293417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206723, d292670, d293417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206724 q = 1) (hb : d292671 q = 1) : d293418 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d206724, d292671, d293418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d206724, d292671, d293418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d206753 q = 1) (hb : d292677 q = 1) : d293813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d206753, d292677, d293813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d206753, d292677, d293813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d206754 q = 1) (hb : d292692 q = 1) : d294967 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d206754, d292692, d294967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d206754, d292692, d294967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro75755 (p : Pattern) (ha : d292662 p = 1) (hb : d293802 p = 1) : d294956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292648 q = 1) (hb : d293792 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292648, d293792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292648, d293792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75733 q ha hb
  have h2 (q : Pattern) (ha : d292559 q = 1) (hb : d293694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292559, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75733 q ha hb
    | true =>
      simp only [d292559, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292649 q = 1) (hb : d293793 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292649, d293793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292649, d293793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292560 q = 1) (hb : d293695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292560, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292560, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292650 q = 1) (hb : d293794 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292650, d293794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292650, d293794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292651 q = 1) (hb : d293795 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292651, d293795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292651, d293795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292652 q = 1) (hb : d293568 q = 1) : d294951 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292652, d293568, d294951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292652, d293568, d294951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75734 q ha hb
  have h8 (q : Pattern) (ha : d292565 q = 1) (hb : d293493 q = 1) : d294873 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292565, d293493, d294873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75734 q ha hb
    | true =>
      simp only [d292565, d293493, d294873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292653 q = 1) (hb : d293569 q = 1) : d294952 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292653, d293569, d294952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292653, d293569, d294952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292566 q = 1) (hb : d293494 q = 1) : d294874 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292566, d293494, d294874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292566, d293494, d294874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d292654 q = 1) (hb : d293570 q = 1) : d294953 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292654, d293570, d294953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292654, d293570, d294953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d292655 q = 1) (hb : d293571 q = 1) : d294954 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292655, d293571, d294954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292655, d293571, d294954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d292656 q = 1) (hb : d293796 q = 1) : d294955 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292656, d293796, d294955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292656, d293796, d294955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292652 q = 1) (hb : d293797 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292652, d293797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292652, d293797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75735 q ha hb
  have h15 (q : Pattern) (ha : d292565 q = 1) (hb : d293702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292565, d293702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75735 q ha hb
    | true =>
      simp only [d292565, d293702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d292653 q = 1) (hb : d293798 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292653, d293798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d292653, d293798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d292566 q = 1) (hb : d293703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292566, d293703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292566, d293703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d292654 q = 1) (hb : d293799 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292654, d293799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d292654, d293799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d292655 q = 1) (hb : d293800 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292655, d293800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d292655, d293800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d292657 q = 1) (hb : d293573 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292657, d293573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292657, d293573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75717 q ha hb
  have h21 (q : Pattern) (ha : d292474 q = 1) (hb : d293501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292474, d293501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75717 q ha hb
    | true =>
      simp only [d292474, d293501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d292658 q = 1) (hb : d293574 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292658, d293574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d292658, d293574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d292475 q = 1) (hb : d293502 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292475, d293502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d292475, d293502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d292659 q = 1) (hb : d293575 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292659, d293575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d292659, d293575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d292660 q = 1) (hb : d293576 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292660, d293576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d292660, d293576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d292661 q = 1) (hb : d293801 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292661, d293801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d292661, d293801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d292662 q = 1) (hb : d293802 q = 1) : d294956 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292662, d293802, d294956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292662, d293802, d294956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro75756 (p : Pattern) (ha : d292673 p = 1) (hb : d293804 p = 1) : d294958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292663 q = 1) (hb : d293568 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292663, d293568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292663, d293568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75716 q ha hb
  have h2 (q : Pattern) (ha : d292468 q = 1) (hb : d293493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292468, d293493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75716 q ha hb
    | true =>
      simp only [d292468, d293493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292664 q = 1) (hb : d293569 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292664, d293569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292664, d293569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292469 q = 1) (hb : d293494 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292469, d293494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292469, d293494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292665 q = 1) (hb : d293570 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292665, d293570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292665, d293570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292666 q = 1) (hb : d293571 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292666, d293571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292666, d293571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d206701 q = 1) (hb : d292657 q = 1) : d294728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d206701, d292657, d294728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206701, d292657, d294728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75715 q ha hb
  have h8 (q : Pattern) (ha : d206487 q = 1) (hb : d292474 q = 1) : d294650 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d206487, d292474, d294650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75715 q ha hb
    | true =>
      simp only [d206487, d292474, d294650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d206702 q = 1) (hb : d292658 q = 1) : d294729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d206702, d292658, d294729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d206702, d292658, d294729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d206488 q = 1) (hb : d292475 q = 1) : d294651 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d206488, d292475, d294651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d206488, d292475, d294651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d206703 q = 1) (hb : d292659 q = 1) : d294730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d206703, d292659, d294730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d206703, d292659, d294730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d206704 q = 1) (hb : d292660 q = 1) : d294731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d206704, d292660, d294731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d206704, d292660, d294731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d292667 q = 1) (hb : d293803 q = 1) : d294732 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292667, d293803, d294732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292667, d293803, d294732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d292657 q = 1) (hb : d293573 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292657, d293573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292657, d293573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75717 q ha hb
  have h15 (q : Pattern) (ha : d292474 q = 1) (hb : d293501 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292474, d293501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75717 q ha hb
    | true =>
      simp only [d292474, d293501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d292658 q = 1) (hb : d293574 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292658, d293574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d292658, d293574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d292475 q = 1) (hb : d293502 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292475, d293502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292475, d293502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d292659 q = 1) (hb : d293575 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292659, d293575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d292659, d293575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d292660 q = 1) (hb : d293576 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292660, d293576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d292660, d293576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d292671 q = 1) (hb : d293418 q = 1) : d293418 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d292672 q = 1) (hb : d293577 q = 1) : d294957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292672, d293577, d294957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d292672, d293577, d294957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d292673 q = 1) (hb : d293804 q = 1) : d294958 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292673, d293804, d294958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292673, d293804, d294958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro75757 (p : Pattern) (ha : d292678 p = 1) (hb : d293814 p = 1) : d294962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292657 q = 1) (hb : d293808 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292657, d293808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292657, d293808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75737 q ha hb
  have h2 (q : Pattern) (ha : d292474 q = 1) (hb : d293714 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292474, d293714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75737 q ha hb
    | true =>
      simp only [d292474, d293714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292658 q = 1) (hb : d293809 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292658, d293809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292658, d293809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292475 q = 1) (hb : d293715 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292475, d293715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292475, d293715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292659 q = 1) (hb : d293810 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292659, d293810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292659, d293810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292660 q = 1) (hb : d293811 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292660, d293811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292660, d293811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292671 q = 1) (hb : d293418 q = 1) : d293418 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d292672 q = 1) (hb : d293812 q = 1) : d294957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292672, d293812, d294957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292672, d293812, d294957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292677 q = 1) (hb : d293813 q = 1) : d293813 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d292678 q = 1) (hb : d293814 q = 1) : d294962 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292678, d293814, d294962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292678, d293814, d294962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75758 (p : Pattern) (ha : d292688 p = 1) (hb : d293819 p = 1) : d294962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d206701 q = 1) (hb : d292683 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d206701, d292683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206701, d292683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75719 q ha hb
  have h2 (q : Pattern) (ha : d206487 q = 1) (hb : d292489 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d206487, d292489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75719 q ha hb
    | true =>
      simp only [d206487, d292489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d206702 q = 1) (hb : d292684 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d206702, d292684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206702, d292684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d206488 q = 1) (hb : d292490 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d206488, d292490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206488, d292490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d206703 q = 1) (hb : d292685 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d206703, d292685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206703, d292685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206704 q = 1) (hb : d292686 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d206704, d292686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d206704, d292686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d206721 q = 1) (hb : d292668 q = 1) : d293415 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d206721, d292668, d293415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206721, d292668, d293415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75713 q ha hb
  have h8 (q : Pattern) (ha : d206497 q = 1) (hb : d292481 q = 1) : d293372 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d206497, d292481, d293372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75713 q ha hb
    | true =>
      simp only [d206497, d292481, d293372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d206722 q = 1) (hb : d292669 q = 1) : d293416 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d206722, d292669, d293416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d206722, d292669, d293416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d206498 q = 1) (hb : d292482 q = 1) : d293373 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d206498, d292482, d293373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d206498, d292482, d293373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d206723 q = 1) (hb : d292670 q = 1) : d293417 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d206723, d292670, d293417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d206723, d292670, d293417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d206724 q = 1) (hb : d292671 q = 1) : d293418 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d206724, d292671, d293418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d206724, d292671, d293418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d206725 q = 1) (hb : d292687 q = 1) : d294957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d206725, d292687, d294957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d206725, d292687, d294957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292677 q = 1) (hb : d293813 q = 1) : d293813 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d292688 q = 1) (hb : d293819 q = 1) : d294962 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292688, d293819, d294962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d292688, d293819, d294962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75759 (p : Pattern) (ha : d292698 p = 1) (hb : d293828 p = 1) : d294973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292674 q = 1) (hb : d293805 q = 1) : d294959 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292674, d293805, d294959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75755 q ha hb
    | true =>
      simp only [d292674, d293805, d294959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75756 q ha hb
  have h2 (q : Pattern) (ha : d292675 q = 1) (hb : d293806 q = 1) : d294960 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292675, d293806, d294960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292675, d293806, d294960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292676 q = 1) (hb : d293807 q = 1) : d294961 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292676, d293807, d294961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292676, d293807, d294961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292679 q = 1) (hb : d293815 q = 1) : d294963 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292679, d293815, d294963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75756 q ha hb
    | true =>
      simp only [d292679, d293815, d294963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75757 q ha hb
  have h5 (q : Pattern) (ha : d292680 q = 1) (hb : d293816 q = 1) : d294964 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292680, d293816, d294964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292680, d293816, d294964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292681 q = 1) (hb : d293817 q = 1) : d294965 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292681, d293817, d294965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292681, d293817, d294965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292682 q = 1) (hb : d293818 q = 1) : d294966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292682, d293818, d294966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292682, d293818, d294966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292689 q = 1) (hb : d293820 q = 1) : d294963 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292689, d293820, d294963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75756 q ha hb
    | true =>
      simp only [d292689, d293820, d294963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75758 q ha hb
  have h9 (q : Pattern) (ha : d292690 q = 1) (hb : d293821 q = 1) : d294964 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292690, d293821, d294964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292690, d293821, d294964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292691 q = 1) (hb : d293822 q = 1) : d294965 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292691, d293822, d294965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292691, d293822, d294965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292693 q = 1) (hb : d293823 q = 1) : d294968 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292693, d293823, d294968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75758 q ha hb
    | true =>
      simp only [d292693, d293823, d294968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75754 q hb ha
  have h12 (q : Pattern) (ha : d292694 q = 1) (hb : d293824 q = 1) : d294969 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292694, d293824, d294969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292694, d293824, d294969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d292695 q = 1) (hb : d293825 q = 1) : d294970 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292695, d293825, d294970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292695, d293825, d294970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292696 q = 1) (hb : d293826 q = 1) : d294971 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292696, d293826, d294971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292696, d293826, d294971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d292697 q = 1) (hb : d293827 q = 1) : d294972 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292697, d293827, d294972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292697, d293827, d294972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d292698 q = 1) (hb : d293828 q = 1) : d294973 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292698, d293828, d294973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292698, d293828, d294973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro75760 (p : Pattern) (ha : d292703 p = 1) (hb : d293833 p = 1) : d294978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292689 q = 1) (hb : d293820 q = 1) : d294963 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292689, d293820, d294963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75756 q ha hb
    | true =>
      simp only [d292689, d293820, d294963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75758 q ha hb
  have h2 (q : Pattern) (ha : d292690 q = 1) (hb : d293821 q = 1) : d294964 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292690, d293821, d294964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292690, d293821, d294964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292691 q = 1) (hb : d293822 q = 1) : d294965 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292691, d293822, d294965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292691, d293822, d294965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292693 q = 1) (hb : d293823 q = 1) : d294968 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292693, d293823, d294968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75758 q ha hb
    | true =>
      simp only [d292693, d293823, d294968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75754 q hb ha
  have h5 (q : Pattern) (ha : d292694 q = 1) (hb : d293824 q = 1) : d294969 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292694, d293824, d294969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292694, d293824, d294969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292695 q = 1) (hb : d293825 q = 1) : d294970 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292695, d293825, d294970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292695, d293825, d294970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292696 q = 1) (hb : d293826 q = 1) : d294971 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292696, d293826, d294971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292696, d293826, d294971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292701 q = 1) (hb : d293831 q = 1) : d294976 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292701, d293831, d294976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292701, d293831, d294976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292702 q = 1) (hb : d293832 q = 1) : d294977 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292702, d293832, d294977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292702, d293832, d294977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292703 q = 1) (hb : d293833 q = 1) : d294978 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292703, d293833, d294978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292703, d293833, d294978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro75761 (p : Pattern) (ha : d292709 p = 1) (hb : d293839 p = 1) : d294984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292699 q = 1) (hb : d293829 q = 1) : d294974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292699, d293829, d294974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75759 q ha hb
    | true =>
      simp only [d292699, d293829, d294974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292700 q = 1) (hb : d293830 q = 1) : d294975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292700, d293830, d294975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292700, d293830, d294975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292704 q = 1) (hb : d293834 q = 1) : d294979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292704, d293834, d294979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75760 q ha hb
    | true =>
      simp only [d292704, d293834, d294979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292705 q = 1) (hb : d293835 q = 1) : d294980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292705, d293835, d294980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292705, d293835, d294980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292706 q = 1) (hb : d293836 q = 1) : d294981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292706, d293836, d294981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292706, d293836, d294981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292707 q = 1) (hb : d293837 q = 1) : d294982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292707, d293837, d294982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292707, d293837, d294982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292708 q = 1) (hb : d293838 q = 1) : d294983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292708, d293838, d294983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292708, d293838, d294983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292709 q = 1) (hb : d293839 q = 1) : d294984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292709, d293839, d294984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292709, d293839, d294984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75762 (p : Pattern) (ha : d292711 p = 1) (hb : d293841 p = 1) : d294986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292693 q = 1) (hb : d293823 q = 1) : d294968 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292693, d293823, d294968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75758 q ha hb
    | true =>
      simp only [d292693, d293823, d294968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75754 q hb ha
  have h2 (q : Pattern) (ha : d292694 q = 1) (hb : d293824 q = 1) : d294969 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292694, d293824, d294969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292694, d293824, d294969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292695 q = 1) (hb : d293825 q = 1) : d294970 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292695, d293825, d294970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292695, d293825, d294970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292701 q = 1) (hb : d293831 q = 1) : d294976 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292701, d293831, d294976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292701, d293831, d294976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292710 q = 1) (hb : d293840 q = 1) : d294985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292710, d293840, d294985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292710, d293840, d294985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292711 q = 1) (hb : d293841 q = 1) : d294986 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292711, d293841, d294986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292711, d293841, d294986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75763 (p : Pattern) (ha : d292717 p = 1) (hb : d293847 p = 1) : d294992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292704 q = 1) (hb : d293834 q = 1) : d294979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292704, d293834, d294979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75760 q ha hb
    | true =>
      simp only [d292704, d293834, d294979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292705 q = 1) (hb : d293835 q = 1) : d294980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292705, d293835, d294980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292705, d293835, d294980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292712 q = 1) (hb : d293842 q = 1) : d294987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292712, d293842, d294987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75762 q ha hb
    | true =>
      simp only [d292712, d293842, d294987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292713 q = 1) (hb : d293843 q = 1) : d294988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292713, d293843, d294988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292713, d293843, d294988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292714 q = 1) (hb : d293844 q = 1) : d294989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292714, d293844, d294989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292714, d293844, d294989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292715 q = 1) (hb : d293845 q = 1) : d294990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292715, d293845, d294990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292715, d293845, d294990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292716 q = 1) (hb : d293846 q = 1) : d294991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292716, d293846, d294991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292716, d293846, d294991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292717 q = 1) (hb : d293847 q = 1) : d294992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292717, d293847, d294992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292717, d293847, d294992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75764 (p : Pattern) (ha : d292728 p = 1) (hb : d293853 p = 1) : d294998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292704 q = 1) (hb : d293834 q = 1) : d294979 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292704, d293834, d294979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75760 q ha hb
    | true =>
      simp only [d292704, d293834, d294979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292705 q = 1) (hb : d293835 q = 1) : d294980 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292705, d293835, d294980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292705, d293835, d294980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292725 q = 1) (hb : d293850 q = 1) : d294995 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292725, d293850, d294995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292725, d293850, d294995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292726 q = 1) (hb : d293851 q = 1) : d294996 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292726, d293851, d294996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292726, d293851, d294996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292727 q = 1) (hb : d293852 q = 1) : d294997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292727, d293852, d294997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292727, d293852, d294997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292728 q = 1) (hb : d293853 q = 1) : d294998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292728, d293853, d294998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292728, d293853, d294998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75765 (p : Pattern) (ha : d292734 p = 1) (hb : d293859 p = 1) : d295004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292718 q = 1) (hb : d293848 q = 1) : d294993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292718, d293848, d294993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75761 q ha hb
    | true =>
      simp only [d292718, d293848, d294993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75763 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292723 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292724 q = 1) (hb : d293849 q = 1) : d294994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292724, d293849, d294994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292724, d293849, d294994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d292729 q = 1) (hb : d293854 q = 1) : d294999 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292729, d293854, d294999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75764 q ha hb
    | true =>
      simp only [d292729, d293854, d294999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292730 q = 1) (hb : d293855 q = 1) : d295000 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292730, d293855, d295000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292730, d293855, d295000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292731 q = 1) (hb : d293856 q = 1) : d295001 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292731, d293856, d295001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292731, d293856, d295001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292732 q = 1) (hb : d293857 q = 1) : d295002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292732, d293857, d295002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292732, d293857, d295002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292733 q = 1) (hb : d293858 q = 1) : d295003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292733, d293858, d295003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292733, d293858, d295003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292734 q = 1) (hb : d293859 q = 1) : d295004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292734, d293859, d295004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292734, d293859, d295004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro75766 (p : Pattern) (ha : d292722 p = 1) (hb : d293864 p = 1) : d295009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292712 q = 1) (hb : d293842 q = 1) : d294987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292712, d293842, d294987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75762 q ha hb
    | true =>
      simp only [d292712, d293842, d294987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292713 q = 1) (hb : d293843 q = 1) : d294988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292713, d293843, d294988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292713, d293843, d294988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292719 q = 1) (hb : d293861 q = 1) : d295006 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292719, d293861, d295006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292719, d293861, d295006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292720 q = 1) (hb : d293862 q = 1) : d295007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292720, d293862, d295007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292720, d293862, d295007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292721 q = 1) (hb : d293863 q = 1) : d295008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292721, d293863, d295008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292721, d293863, d295008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292722 q = 1) (hb : d293864 q = 1) : d295009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292722, d293864, d295009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292722, d293864, d295009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75767 (p : Pattern) (ha : d292741 p = 1) (hb : d293870 p = 1) : d295015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292736 q = 1) (hb : d293865 q = 1) : d295010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292736, d293865, d295010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75766 q ha hb
    | true =>
      simp only [d292736, d293865, d295010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292737 q = 1) (hb : d293866 q = 1) : d295011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292737, d293866, d295011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292737, d293866, d295011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292738 q = 1) (hb : d293867 q = 1) : d295012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292738, d293867, d295012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292738, d293867, d295012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292739 q = 1) (hb : d293868 q = 1) : d295013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292739, d293868, d295013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292739, d293868, d295013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292740 q = 1) (hb : d293869 q = 1) : d295014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292740, d293869, d295014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292740, d293869, d295014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292741 q = 1) (hb : d293870 q = 1) : d295015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292741, d293870, d295015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292741, d293870, d295015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75768 (p : Pattern) (ha : d292747 p = 1) (hb : d293876 p = 1) : d295021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292527 q = 1) (hb : d293663 q = 1) : d294840 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292527, d293663, d294840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292527, d293663, d294840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75725 q ha hb
  have h2 (q : Pattern) (ha : d292528 q = 1) (hb : d293664 q = 1) : d294841 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292528, d293664, d294841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292528, d293664, d294841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292537 q = 1) (hb : d293673 q = 1) : d294850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292537, d293673, d294850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75725 q ha hb
    | true =>
      simp only [d292537, d293673, d294850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75728 q ha hb
  have h4 (q : Pattern) (ha : d292538 q = 1) (hb : d293674 q = 1) : d294851 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292538, d293674, d294851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292538, d293674, d294851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292539 q = 1) (hb : d293675 q = 1) : d294852 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292539, d293675, d294852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292539, d293675, d294852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292621 q = 1) (hb : d293765 q = 1) : d294924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292621, d293765, d294924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75742 q ha hb
    | true =>
      simp only [d292621, d293765, d294924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75749 q ha hb
  have h7 (q : Pattern) (ha : d292634 q = 1) (hb : d293778 q = 1) : d294937 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292634, d293778, d294937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75750 q ha hb
    | true =>
      simp only [d292634, d293778, d294937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75751 q ha hb
  have h8 (q : Pattern) (ha : d292635 q = 1) (hb : d293779 q = 1) : d294938 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292635, d293779, d294938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292635, d293779, d294938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292636 q = 1) (hb : d293780 q = 1) : d294939 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292636, d293780, d294939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292636, d293780, d294939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d292637 q = 1) (hb : d293781 q = 1) : d294940 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292637, d293781, d294940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292637, d293781, d294940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292641 q = 1) (hb : d293785 q = 1) : d294944 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292641, d293785, d294944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292641, d293785, d294944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75752 q ha hb
  have h12 (q : Pattern) (ha : d292643 q = 1) (hb : d293787 q = 1) : d294946 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292643, d293787, d294946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292643, d293787, d294946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75753 q ha hb
  have h13 (q : Pattern) (ha : d292644 q = 1) (hb : d293788 q = 1) : d294947 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292644, d293788, d294947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292644, d293788, d294947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292645 q = 1) (hb : d293789 q = 1) : d294948 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292645, d293789, d294948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292645, d293789, d294948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d292646 q = 1) (hb : d293790 q = 1) : d294949 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292646, d293790, d294949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d292646, d293790, d294949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d292647 q = 1) (hb : d293791 q = 1) : d294950 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292647, d293791, d294950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292647, d293791, d294950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d292735 q = 1) (hb : d293860 q = 1) : d295005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292735, d293860, d295005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292735, d293860, d295005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75765 q ha hb
  have h18 (q : Pattern) (ha : d292742 q = 1) (hb : d293871 q = 1) : d295016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292742, d293871, d295016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292742, d293871, d295016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75767 q ha hb
  have h19 (q : Pattern) (ha : d292743 q = 1) (hb : d293872 q = 1) : d295017 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292743, d293872, d295017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d292743, d293872, d295017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d292744 q = 1) (hb : d293873 q = 1) : d295018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292744, d293873, d295018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d292744, d293873, d295018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d292745 q = 1) (hb : d293874 q = 1) : d295019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292745, d293874, d295019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d292745, d293874, d295019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d292746 q = 1) (hb : d293875 q = 1) : d295020 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292746, d293875, d295020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d292746, d293875, d295020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d292747 q = 1) (hb : d293876 q = 1) : d295021 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d292747, d293876, d295021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d292747, d293876, d295021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro75769 (p : Pattern) (ha : d292753 p = 1) (hb : d293882 p = 1) : d295027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292748 q = 1) (hb : d293877 q = 1) : d295022 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d292748, d293877, d295022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292748, d293877, d295022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75768 q ha hb
  have h2 (q : Pattern) (ha : d292749 q = 1) (hb : d293878 q = 1) : d295023 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d292749, d293878, d295023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292749, d293878, d295023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292750 q = 1) (hb : d293879 q = 1) : d295024 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d292750, d293879, d295024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292750, d293879, d295024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292751 q = 1) (hb : d293880 q = 1) : d295025 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d292751, d293880, d295025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292751, d293880, d295025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292752 q = 1) (hb : d293881 q = 1) : d295026 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d292752, d293881, d295026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292752, d293881, d295026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292753 q = 1) (hb : d293882 q = 1) : d295027 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d292753, d293882, d295027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292753, d293882, d295027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75770 (p : Pattern) (ha : d292758 p = 1) (hb : d293693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31303 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31303, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75017 q ha hb
    | true =>
      simp only [d31303, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31304 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31304, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31304, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31736 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31737 q = 1) (hb : d292757 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31737, d292757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31737, d292757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31738 q = 1) (hb : d292758 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31738, d292758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31738, d292758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d292758 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d292758 q = 1) (hb : d293693 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d293693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d293693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro75771 (p : Pattern) (ha : d292764 p = 1) (hb : d293889 p = 1) : d294872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32141 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32141, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35622 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32142 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32142, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52986 q = 1) (hb : d293886 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d293886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d31739 q = 1) : d31739 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d292763 q = 1) (hb : d293887 q = 1) : d294870 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d292763, d293887, d294870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292763, d293887, d294870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d292764 q = 1) (hb : d293888 q = 1) : d294871 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d292764, d293888, d294871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292764, d293888, d294871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d292764 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d292764 q = 1) (hb : d293889 q = 1) : d294872 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d293889, d294872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293889, d294872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro75772 (p : Pattern) (ha : d292764 p = 1) (hb : d293898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52983 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32166 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32166, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32166, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32167 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32167, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32167, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52986 q = 1) (hb : d293895 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d293895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d292763 q = 1) (hb : d293896 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d292763, d293896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292763, d293896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d292764 q = 1) (hb : d293897 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d292764, d293897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292764, d293897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d292764 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d292764 q = 1) (hb : d293898 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d293898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro75773 (p : Pattern) (ha : d292777 p = 1) (hb : d293911 p = 1) : d295032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292759 q = 1) (hb : d293694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292759, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75770 q ha hb
    | true =>
      simp only [d292759, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292760 q = 1) (hb : d293695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292760, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292760, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292761 q = 1) (hb : d293696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292761, d293696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292761, d293696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292762 q = 1) (hb : d293697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292762, d293697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292762, d293697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292765 q = 1) (hb : d293890 q = 1) : d294873 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292765, d293890, d294873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75771 q ha hb
    | true =>
      simp only [d292765, d293890, d294873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292766 q = 1) (hb : d293891 q = 1) : d294874 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292766, d293891, d294874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292766, d293891, d294874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292767 q = 1) (hb : d293892 q = 1) : d294875 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292767, d293892, d294875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292767, d293892, d294875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292768 q = 1) (hb : d293893 q = 1) : d294876 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292768, d293893, d294876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292768, d293893, d294876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292769 q = 1) (hb : d293894 q = 1) : d294877 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292769, d293894, d294877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292769, d293894, d294877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292765 q = 1) (hb : d293899 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292765, d293899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75772 q ha hb
    | true =>
      simp only [d292765, d293899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d292766 q = 1) (hb : d293900 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292766, d293900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292766, d293900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d292767 q = 1) (hb : d293901 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292767, d293901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292767, d293901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d292768 q = 1) (hb : d293902 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292768, d293902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d292768, d293902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d292775 q = 1) (hb : d293909 q = 1) : d293909 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d292776 q = 1) (hb : d293910 q = 1) : d295031 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292776, d293910, d295031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292776, d293910, d295031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d292777 q = 1) (hb : d293911 q = 1) : d295032 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292777, d293911, d295032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292777, d293911, d295032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro75774 (p : Pattern) (ha : d292771 p = 1) (hb : d293915 p = 1) : d293905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d25764 q = 1) : d25764 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d32187 q = 1) (hb : d53016 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32187, d53016, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d32187, d53016, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15069 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32188 q = 1) (hb : d53017 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32188, d53017, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32188, d53017, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53017 q = 1) (hb : d293912 q = 1) : d31739 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d293912, d31739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293912, d31739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1564 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15069 q ha hb
    | true =>
      simp only [d1564, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1565 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1565, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29564 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d292770 q = 1) (hb : d293913 q = 1) : d293903 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d292770, d293913, d293903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292770, d293913, d293903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d292771 q = 1) (hb : d293914 q = 1) : d293904 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d292771, d293914, d293904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d292771, d293914, d293904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d292771 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d292771 q = 1) (hb : d293915 q = 1) : d293905 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d293915, d293905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293915, d293905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro75775 (p : Pattern) (ha : d292779 p = 1) (hb : d293889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32141 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32141, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35622 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32142 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32142, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52986 q = 1) (hb : d293886 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d293886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199014 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25765 q = 1) (hb : d199013 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d199013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61118 q ha hb
    | true =>
      simp only [d25765, d199013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25766 q = 1) (hb : d199014 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d199014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25766, d199014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d31739 q = 1) (hb : d199014 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292778 q = 1) (hb : d293887 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d292778, d293887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292778, d293887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d292779 q = 1) (hb : d293888 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d292779, d293888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292779, d293888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d292779 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d292779 q = 1) (hb : d293889 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d293889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro75776 (p : Pattern) (ha : d292786 p = 1) (hb : d293922 p = 1) : d295033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292780 q = 1) (hb : d293890 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292780, d293890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75775 q ha hb
    | true =>
      simp only [d292780, d293890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292781 q = 1) (hb : d293891 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292781, d293891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292781, d293891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292782 q = 1) (hb : d293892 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292782, d293892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292782, d293892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292783 q = 1) (hb : d293893 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292783, d293893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292783, d293893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292772 q = 1) (hb : d293916 q = 1) : d293906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
    | true =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292773 q = 1) (hb : d293917 q = 1) : d293907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292774 q = 1) (hb : d293918 q = 1) : d293908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292774, d293918, d293908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292774, d293918, d293908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292775 q = 1) (hb : d293919 q = 1) : d293909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292775, d293919, d293909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292775, d293919, d293909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292784 q = 1) (hb : d293920 q = 1) : d295031 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292784, d293920, d295031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292784, d293920, d295031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292785 q = 1) (hb : d293921 q = 1) : d293921 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d292786 q = 1) (hb : d293922 q = 1) : d295033 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292786, d293922, d295033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292786, d293922, d295033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75777 (p : Pattern) (ha : d292790 p = 1) (hb : d293927 p = 1) : d295037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292772 q = 1) (hb : d293916 q = 1) : d293906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
    | true =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292773 q = 1) (hb : d293917 q = 1) : d293907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292774 q = 1) (hb : d293918 q = 1) : d293908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292774, d293918, d293908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292774, d293918, d293908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292775 q = 1) (hb : d293919 q = 1) : d293909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292775, d293919, d293909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292775, d293919, d293909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292785 q = 1) (hb : d293926 q = 1) : d293921 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292785, d293926, d293921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292785, d293926, d293921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292790 q = 1) (hb : d293927 q = 1) : d295037 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292790, d293927, d295037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292790, d293927, d295037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75778 (p : Pattern) (ha : d292797 p = 1) (hb : d293934 p = 1) : d295044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292787 q = 1) (hb : d293923 q = 1) : d295034 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292787, d293923, d295034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75773 q ha hb
    | true =>
      simp only [d292787, d293923, d295034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75776 q ha hb
  have h2 (q : Pattern) (ha : d292788 q = 1) (hb : d293924 q = 1) : d295035 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292788, d293924, d295035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292788, d293924, d295035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292789 q = 1) (hb : d293925 q = 1) : d295036 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292789, d293925, d295036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292789, d293925, d295036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292791 q = 1) (hb : d293928 q = 1) : d295038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292791, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75776 q ha hb
    | true =>
      simp only [d292791, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75777 q ha hb
  have h5 (q : Pattern) (ha : d292792 q = 1) (hb : d293929 q = 1) : d295039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292792, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292792, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292793 q = 1) (hb : d293930 q = 1) : d295040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292793, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292793, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292794 q = 1) (hb : d293931 q = 1) : d295041 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292794, d293931, d295041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292794, d293931, d295041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292795 q = 1) (hb : d293932 q = 1) : d295042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292795, d293932, d295042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292795, d293932, d295042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292796 q = 1) (hb : d293933 q = 1) : d295043 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292796, d293933, d295043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292796, d293933, d295043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292797 q = 1) (hb : d293934 q = 1) : d295044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292797, d293934, d295044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292797, d293934, d295044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro75779 (p : Pattern) (ha : d292801 p = 1) (hb : d293938 p = 1) : d295048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292791 q = 1) (hb : d293928 q = 1) : d295038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292791, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75776 q ha hb
    | true =>
      simp only [d292791, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75777 q ha hb
  have h2 (q : Pattern) (ha : d292792 q = 1) (hb : d293929 q = 1) : d295039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292792, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292792, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292793 q = 1) (hb : d293930 q = 1) : d295040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292793, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292793, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292795 q = 1) (hb : d293932 q = 1) : d295042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292795, d293932, d295042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292795, d293932, d295042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292800 q = 1) (hb : d293937 q = 1) : d295047 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292800, d293937, d295047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292800, d293937, d295047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292801 q = 1) (hb : d293938 q = 1) : d295048 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292801, d293938, d295048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292801, d293938, d295048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75780 (p : Pattern) (ha : d292807 p = 1) (hb : d293944 p = 1) : d295054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292798 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75778 q ha hb
    | true =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292799 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292804 q = 1) (hb : d293941 q = 1) : d295051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292805 q = 1) (hb : d293942 q = 1) : d295052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292805, d293942, d295052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292805, d293942, d295052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292806 q = 1) (hb : d293943 q = 1) : d295053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292806, d293943, d295053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292806, d293943, d295053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292807 q = 1) (hb : d293944 q = 1) : d295054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292807, d293944, d295054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292807, d293944, d295054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75781 (p : Pattern) (ha : d292811 p = 1) (hb : d293948 p = 1) : d295058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292808 q = 1) (hb : d293945 q = 1) : d295055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292809 q = 1) (hb : d293946 q = 1) : d295056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292809, d293946, d295056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292809, d293946, d295056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292810 q = 1) (hb : d293947 q = 1) : d295057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292810, d293947, d295057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292810, d293947, d295057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292811 q = 1) (hb : d293948 q = 1) : d295058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292811, d293948, d295058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292811, d293948, d295058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75782 (p : Pattern) (ha : d292817 p = 1) (hb : d293954 p = 1) : d295064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292812 q = 1) (hb : d293949 q = 1) : d295059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75780 q ha hb
    | true =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75781 q ha hb
  have h2 (q : Pattern) (ha : d292813 q = 1) (hb : d293950 q = 1) : d295060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292813, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292813, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292814 q = 1) (hb : d293951 q = 1) : d295061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292814, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292814, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292815 q = 1) (hb : d293952 q = 1) : d295062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292815, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292815, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292816 q = 1) (hb : d293953 q = 1) : d295063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292816, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292816, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292817 q = 1) (hb : d293954 q = 1) : d295064 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292817, d293954, d295064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292817, d293954, d295064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75783 (p : Pattern) (ha : d292820 p = 1) (hb : d293957 p = 1) : d295067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292798 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75778 q ha hb
    | true =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292799 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292804 q = 1) (hb : d293941 q = 1) : d295051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292805 q = 1) (hb : d293942 q = 1) : d295052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292805, d293942, d295052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292805, d293942, d295052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292806 q = 1) (hb : d293943 q = 1) : d295053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292806, d293943, d295053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292806, d293943, d295053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292820 q = 1) (hb : d293957 q = 1) : d295067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292820, d293957, d295067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292820, d293957, d295067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75784 (p : Pattern) (ha : d292821 p = 1) (hb : d293958 p = 1) : d295068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292808 q = 1) (hb : d293945 q = 1) : d295055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292809 q = 1) (hb : d293946 q = 1) : d295056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292809, d293946, d295056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292809, d293946, d295056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292810 q = 1) (hb : d293947 q = 1) : d295057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292810, d293947, d295057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292810, d293947, d295057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292821 q = 1) (hb : d293958 q = 1) : d295068 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292821, d293958, d295068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292821, d293958, d295068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75785 (p : Pattern) (ha : d292827 p = 1) (hb : d293964 p = 1) : d295074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292812 q = 1) (hb : d293949 q = 1) : d295059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75780 q ha hb
    | true =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75781 q ha hb
  have h2 (q : Pattern) (ha : d292813 q = 1) (hb : d293950 q = 1) : d295060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292813, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292813, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292814 q = 1) (hb : d293951 q = 1) : d295061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292814, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292814, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292815 q = 1) (hb : d293952 q = 1) : d295062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292815, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292815, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292816 q = 1) (hb : d293953 q = 1) : d295063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292816, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292816, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292822 q = 1) (hb : d293959 q = 1) : d295069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292822, d293959, d295069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75783 q ha hb
    | true =>
      simp only [d292822, d293959, d295069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75784 q ha hb
  have h7 (q : Pattern) (ha : d292823 q = 1) (hb : d293960 q = 1) : d295070 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292823, d293960, d295070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292823, d293960, d295070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292824 q = 1) (hb : d293961 q = 1) : d295071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292824, d293961, d295071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292824, d293961, d295071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292825 q = 1) (hb : d293962 q = 1) : d295072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292825, d293962, d295072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292825, d293962, d295072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292826 q = 1) (hb : d293963 q = 1) : d295073 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292826, d293963, d295073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292826, d293963, d295073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292827 q = 1) (hb : d293964 q = 1) : d295074 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292827, d293964, d295074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292827, d293964, d295074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75786 (p : Pattern) (ha : d292832 p = 1) (hb : d293969 p = 1) : d295079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292798 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75778 q ha hb
    | true =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292799 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292804 q = 1) (hb : d293941 q = 1) : d295051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292805 q = 1) (hb : d293942 q = 1) : d295052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292805, d293942, d295052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292805, d293942, d295052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292831 q = 1) (hb : d293968 q = 1) : d295078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292831, d293968, d295078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292831, d293968, d295078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292832 q = 1) (hb : d293969 q = 1) : d295079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292832, d293969, d295079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292832, d293969, d295079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75787 (p : Pattern) (ha : d292834 p = 1) (hb : d293971 p = 1) : d295081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292808 q = 1) (hb : d293945 q = 1) : d295055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292809 q = 1) (hb : d293946 q = 1) : d295056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292809, d293946, d295056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292809, d293946, d295056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292833 q = 1) (hb : d293970 q = 1) : d295080 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292833, d293970, d295080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292833, d293970, d295080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292834 q = 1) (hb : d293971 q = 1) : d295081 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292834, d293971, d295081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292834, d293971, d295081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75788 (p : Pattern) (ha : d292841 p = 1) (hb : d293978 p = 1) : d295088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292798 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75778 q ha hb
    | true =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292799 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292804 q = 1) (hb : d293941 q = 1) : d295051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292839 q = 1) (hb : d293976 q = 1) : d295086 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292839, d293976, d295086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292839, d293976, d295086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292840 q = 1) (hb : d293977 q = 1) : d295087 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292840, d293977, d295087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292840, d293977, d295087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292841 q = 1) (hb : d293978 q = 1) : d295088 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292841, d293978, d295088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292841, d293978, d295088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75789 (p : Pattern) (ha : d292844 p = 1) (hb : d293981 p = 1) : d295091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292808 q = 1) (hb : d293945 q = 1) : d295055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292842 q = 1) (hb : d293979 q = 1) : d295089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292842, d293979, d295089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292842, d293979, d295089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292843 q = 1) (hb : d293980 q = 1) : d295090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292843, d293980, d295090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292843, d293980, d295090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292844 q = 1) (hb : d293981 q = 1) : d295091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292844, d293981, d295091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292844, d293981, d295091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75790 (p : Pattern) (ha : d292855 p = 1) (hb : d293987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d292853 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292759 q = 1) (hb : d293694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292759, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75770 q ha hb
    | true =>
      simp only [d292759, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d292760 q = 1) (hb : d293695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292760, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292760, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d292761 q = 1) (hb : d293696 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292761, d293696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292761, d293696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292762 q = 1) (hb : d293697 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292762, d293697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292762, d293697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d292854 q = 1) (hb : d293985 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292854, d293985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292854, d293985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292765 q = 1) (hb : d293899 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292765, d293899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75772 q ha hb
    | true =>
      simp only [d292765, d293899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d292766 q = 1) (hb : d293900 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292766, d293900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292766, d293900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d292767 q = 1) (hb : d293901 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292767, d293901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292767, d293901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292768 q = 1) (hb : d293902 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292768, d293902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292768, d293902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d292769 q = 1) (hb : d293986 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292769, d293986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292769, d293986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d292855 q = 1) (hb : d293987 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292855, d293987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292855, d293987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro75791 (p : Pattern) (ha : d292764 p = 1) (hb : d293993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32141 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75019 q ha hb
    | true =>
      simp only [d32141, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35622 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32142 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32142, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52986 q = 1) (hb : d293886 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d293886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d292763 q = 1) (hb : d293991 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d292763, d293991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292763, d293991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d292764 q = 1) (hb : d293992 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d292764, d293992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292764, d293992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d292764 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d292764 q = 1) (hb : d293993 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d293993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro75792 (p : Pattern) (ha : d292859 p = 1) (hb : d293999 p = 1) : d295033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292765 q = 1) (hb : d293994 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292765, d293994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75791 q ha hb
    | true =>
      simp only [d292765, d293994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292766 q = 1) (hb : d293995 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292766, d293995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292766, d293995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292767 q = 1) (hb : d293996 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292767, d293996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292767, d293996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292768 q = 1) (hb : d293997 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292768, d293997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292768, d293997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292775 q = 1) (hb : d293909 q = 1) : d293909 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d292776 q = 1) (hb : d293998 q = 1) : d295031 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292776, d293998, d295031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292776, d293998, d295031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292785 q = 1) (hb : d293921 q = 1) : d293921 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d292859 q = 1) (hb : d293999 q = 1) : d295033 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292859, d293999, d295033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292859, d293999, d295033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75793 (p : Pattern) (ha : d292865 p = 1) (hb : d294005 p = 1) : d295100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292856 q = 1) (hb : d293988 q = 1) : d295095 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292856, d293988, d295095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75790 q ha hb
    | true =>
      simp only [d292856, d293988, d295095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75773 q ha hb
  have h2 (q : Pattern) (ha : d292857 q = 1) (hb : d293989 q = 1) : d295096 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292857, d293989, d295096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292857, d293989, d295096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292858 q = 1) (hb : d293990 q = 1) : d295097 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292858, d293990, d295097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292858, d293990, d295097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292860 q = 1) (hb : d294000 q = 1) : d295034 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292860, d294000, d295034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75773 q ha hb
    | true =>
      simp only [d292860, d294000, d295034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75792 q ha hb
  have h5 (q : Pattern) (ha : d292861 q = 1) (hb : d294001 q = 1) : d295035 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292861, d294001, d295035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292861, d294001, d295035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292862 q = 1) (hb : d294002 q = 1) : d295036 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292862, d294002, d295036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292862, d294002, d295036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292863 q = 1) (hb : d294003 q = 1) : d295098 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292863, d294003, d295098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292863, d294003, d295098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292787 q = 1) (hb : d293923 q = 1) : d295034 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292787, d293923, d295034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75773 q ha hb
    | true =>
      simp only [d292787, d293923, d295034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75776 q ha hb
  have h9 (q : Pattern) (ha : d292788 q = 1) (hb : d293924 q = 1) : d295035 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292788, d293924, d295035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292788, d293924, d295035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292789 q = 1) (hb : d293925 q = 1) : d295036 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292789, d293925, d295036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292789, d293925, d295036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292791 q = 1) (hb : d293928 q = 1) : d295038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292791, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75776 q ha hb
    | true =>
      simp only [d292791, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75777 q ha hb
  have h12 (q : Pattern) (ha : d292792 q = 1) (hb : d293929 q = 1) : d295039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292792, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292792, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d292793 q = 1) (hb : d293930 q = 1) : d295040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292793, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292793, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292794 q = 1) (hb : d293931 q = 1) : d295041 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292794, d293931, d295041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292794, d293931, d295041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d292864 q = 1) (hb : d294004 q = 1) : d295099 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292864, d294004, d295099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292864, d294004, d295099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d292865 q = 1) (hb : d294005 q = 1) : d295100 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292865, d294005, d295100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292865, d294005, d295100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro75794 (p : Pattern) (ha : d292871 p = 1) (hb : d294011 p = 1) : d295106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292866 q = 1) (hb : d294006 q = 1) : d295101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292866, d294006, d295101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75793 q ha hb
    | true =>
      simp only [d292866, d294006, d295101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292867 q = 1) (hb : d294007 q = 1) : d295102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292867, d294007, d295102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292867, d294007, d295102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292798 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75778 q ha hb
    | true =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292799 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292868 q = 1) (hb : d294008 q = 1) : d295103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292868, d294008, d295103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292868, d294008, d295103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292869 q = 1) (hb : d294009 q = 1) : d295104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292869, d294009, d295104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292869, d294009, d295104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292870 q = 1) (hb : d294010 q = 1) : d295105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292870, d294010, d295105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292870, d294010, d295105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292871 q = 1) (hb : d294011 q = 1) : d295106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292871, d294011, d295106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292871, d294011, d295106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75795 (p : Pattern) (ha : d292881 p = 1) (hb : d293922 p = 1) : d295033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292780 q = 1) (hb : d293890 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292780, d293890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75775 q ha hb
    | true =>
      simp only [d292780, d293890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292781 q = 1) (hb : d293891 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292781, d293891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292781, d293891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292782 q = 1) (hb : d293892 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292782, d293892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292782, d293892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292783 q = 1) (hb : d293893 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292783, d293893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292783, d293893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292772 q = 1) (hb : d293916 q = 1) : d293906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
    | true =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292773 q = 1) (hb : d293917 q = 1) : d293907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292774 q = 1) (hb : d293918 q = 1) : d293908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292774, d293918, d293908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292774, d293918, d293908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292775 q = 1) (hb : d293919 q = 1) : d293909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292775, d293919, d293909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292775, d293919, d293909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292784 q = 1) (hb : d293920 q = 1) : d295031 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292784, d293920, d295031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292784, d293920, d295031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292880 q = 1) (hb : d293921 q = 1) : d293921 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d292881 q = 1) (hb : d293922 q = 1) : d295033 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292881, d293922, d295033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292881, d293922, d295033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75796 (p : Pattern) (ha : d292875 p = 1) (hb : d293915 p = 1) : d293905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69216 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d25764 q = 1) : d25764 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d32187 q = 1) (hb : d69215 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32187, d69215, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d32187, d69215, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32188 q = 1) (hb : d69216 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32188, d69216, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32188, d69216, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69216 q = 1) (hb : d293912 q = 1) : d31739 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d293912, d31739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293912, d31739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d29564 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292874 q = 1) (hb : d293913 q = 1) : d293903 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d292874, d293913, d293903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292874, d293913, d293903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d292875 q = 1) (hb : d293914 q = 1) : d293904 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d292875, d293914, d293904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292875, d293914, d293904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d292875 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d292875 q = 1) (hb : d293915 q = 1) : d293905 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d293915, d293905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293915, d293905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro75797 (p : Pattern) (ha : d292882 p = 1) (hb : d293927 p = 1) : d295037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292876 q = 1) (hb : d293916 q = 1) : d293906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292876, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75796 q ha hb
    | true =>
      simp only [d292876, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292877 q = 1) (hb : d293917 q = 1) : d293907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292877, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292877, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292878 q = 1) (hb : d293918 q = 1) : d293908 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292878, d293918, d293908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292878, d293918, d293908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292879 q = 1) (hb : d293919 q = 1) : d293909 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292879, d293919, d293909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292879, d293919, d293909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292880 q = 1) (hb : d293926 q = 1) : d293921 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292880, d293926, d293921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292880, d293926, d293921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292882 q = 1) (hb : d293927 q = 1) : d295037 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292882, d293927, d295037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292882, d293927, d295037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75798 (p : Pattern) (ha : d292888 p = 1) (hb : d293934 p = 1) : d295044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292787 q = 1) (hb : d293923 q = 1) : d295034 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292787, d293923, d295034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75773 q ha hb
    | true =>
      simp only [d292787, d293923, d295034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75776 q ha hb
  have h2 (q : Pattern) (ha : d292788 q = 1) (hb : d293924 q = 1) : d295035 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292788, d293924, d295035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292788, d293924, d295035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292789 q = 1) (hb : d293925 q = 1) : d295036 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292789, d293925, d295036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292789, d293925, d295036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292791 q = 1) (hb : d293928 q = 1) : d295038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292791, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75776 q ha hb
    | true =>
      simp only [d292791, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75777 q ha hb
  have h5 (q : Pattern) (ha : d292792 q = 1) (hb : d293929 q = 1) : d295039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292792, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292792, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292793 q = 1) (hb : d293930 q = 1) : d295040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292793, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292793, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292794 q = 1) (hb : d293931 q = 1) : d295041 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292794, d293931, d295041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292794, d293931, d295041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292883 q = 1) (hb : d293928 q = 1) : d295038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292883, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75795 q ha hb
    | true =>
      simp only [d292883, d293928, d295038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75797 q ha hb
  have h9 (q : Pattern) (ha : d292884 q = 1) (hb : d293929 q = 1) : d295039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292884, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292884, d293929, d295039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292885 q = 1) (hb : d293930 q = 1) : d295040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292885, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292885, d293930, d295040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292886 q = 1) (hb : d293932 q = 1) : d295042 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292886, d293932, d295042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292886, d293932, d295042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d292887 q = 1) (hb : d293933 q = 1) : d295043 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292887, d293933, d295043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292887, d293933, d295043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d292888 q = 1) (hb : d293934 q = 1) : d295044 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292888, d293934, d295044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d292888, d293934, d295044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro75799 (p : Pattern) (ha : d292894 p = 1) (hb : d294017 p = 1) : d295112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292889 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292889, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75798 q ha hb
    | true =>
      simp only [d292889, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292890 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292890, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292890, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292891 q = 1) (hb : d294014 q = 1) : d295109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292891, d294014, d295109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292891, d294014, d295109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292892 q = 1) (hb : d294015 q = 1) : d295110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292892, d294015, d295110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292892, d294015, d295110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292893 q = 1) (hb : d294016 q = 1) : d295111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292893, d294016, d295111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292893, d294016, d295111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292894 q = 1) (hb : d294017 q = 1) : d295112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292894, d294017, d295112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292894, d294017, d295112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75800 (p : Pattern) (ha : d292900 p = 1) (hb : d294023 p = 1) : d295118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292835 q = 1) (hb : d293972 q = 1) : d295082 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292835, d293972, d295082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75786 q ha hb
    | true =>
      simp only [d292835, d293972, d295082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75787 q ha hb
  have h2 (q : Pattern) (ha : d292836 q = 1) (hb : d293973 q = 1) : d295083 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292836, d293973, d295083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292836, d293973, d295083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292837 q = 1) (hb : d293974 q = 1) : d295084 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292837, d293974, d295084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292837, d293974, d295084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292838 q = 1) (hb : d293975 q = 1) : d295085 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292838, d293975, d295085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292838, d293975, d295085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292845 q = 1) (hb : d293982 q = 1) : d295092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292845, d293982, d295092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75788 q ha hb
    | true =>
      simp only [d292845, d293982, d295092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75789 q ha hb
  have h6 (q : Pattern) (ha : d292846 q = 1) (hb : d293983 q = 1) : d295093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292846, d293983, d295093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292846, d293983, d295093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292847 q = 1) (hb : d293984 q = 1) : d295094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292847, d293984, d295094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292847, d293984, d295094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292872 q = 1) (hb : d294012 q = 1) : d295107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292872, d294012, d295107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75794 q ha hb
    | true =>
      simp only [d292872, d294012, d295107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75780 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d292812 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d292873 q = 1) (hb : d294013 q = 1) : d295108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292873, d294013, d295108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292873, d294013, d295108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d292895 q = 1) (hb : d294018 q = 1) : d295113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292895, d294018, d295113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75799 q ha hb
    | true =>
      simp only [d292895, d294018, d295113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d292896 q = 1) (hb : d294019 q = 1) : d295114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292896, d294019, d295114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292896, d294019, d295114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d292897 q = 1) (hb : d294020 q = 1) : d295115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292897, d294020, d295115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292897, d294020, d295115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292898 q = 1) (hb : d294021 q = 1) : d295116 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292898, d294021, d295116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292898, d294021, d295116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d292899 q = 1) (hb : d294022 q = 1) : d295117 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292899, d294022, d295117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292899, d294022, d295117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d292900 q = 1) (hb : d294023 q = 1) : d295118 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292900, d294023, d295118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292900, d294023, d295118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro75801 (p : Pattern) (ha : d292901 p = 1) (hb : d294024 p = 1) : d295119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292798 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75778 q ha hb
    | true =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292799 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292804 q = 1) (hb : d293941 q = 1) : d295051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292805 q = 1) (hb : d293942 q = 1) : d295052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292805, d293942, d295052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292805, d293942, d295052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292831 q = 1) (hb : d293968 q = 1) : d295078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292831, d293968, d295078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292831, d293968, d295078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292901 q = 1) (hb : d294024 q = 1) : d295119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292901, d294024, d295119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292901, d294024, d295119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75802 (p : Pattern) (ha : d292902 p = 1) (hb : d294025 p = 1) : d295120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292808 q = 1) (hb : d293945 q = 1) : d295055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292809 q = 1) (hb : d293946 q = 1) : d295056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292809, d293946, d295056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292809, d293946, d295056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292833 q = 1) (hb : d293970 q = 1) : d295080 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292833, d293970, d295080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292833, d293970, d295080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292902 q = 1) (hb : d294025 q = 1) : d295120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292902, d294025, d295120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292902, d294025, d295120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75803 (p : Pattern) (ha : d292907 p = 1) (hb : d294030 p = 1) : d295125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292798 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75778 q ha hb
    | true =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292799 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292804 q = 1) (hb : d293941 q = 1) : d295051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292804, d293941, d295051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292839 q = 1) (hb : d293976 q = 1) : d295086 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292839, d293976, d295086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292839, d293976, d295086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292840 q = 1) (hb : d293977 q = 1) : d295087 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292840, d293977, d295087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292840, d293977, d295087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292907 q = 1) (hb : d294030 q = 1) : d295125 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292907, d294030, d295125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292907, d294030, d295125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75804 (p : Pattern) (ha : d292908 p = 1) (hb : d294031 p = 1) : d295126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292802 q = 1) (hb : d293939 q = 1) : d295049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75779 q ha hb
    | true =>
      simp only [d292802, d293939, d295049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292803 q = 1) (hb : d293940 q = 1) : d295050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292803, d293940, d295050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292808 q = 1) (hb : d293945 q = 1) : d295055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292808, d293945, d295055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292842 q = 1) (hb : d293979 q = 1) : d295089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292842, d293979, d295089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292842, d293979, d295089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292843 q = 1) (hb : d293980 q = 1) : d295090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292843, d293980, d295090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292843, d293980, d295090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292908 q = 1) (hb : d294031 q = 1) : d295126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292908, d294031, d295126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292908, d294031, d295126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75805 (p : Pattern) (ha : d292912 p = 1) (hb : d294035 p = 1) : d295130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292866 q = 1) (hb : d294006 q = 1) : d295101 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292866, d294006, d295101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75793 q ha hb
    | true =>
      simp only [d292866, d294006, d295101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292867 q = 1) (hb : d294007 q = 1) : d295102 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292867, d294007, d295102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292867, d294007, d295102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292798 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75778 q ha hb
    | true =>
      simp only [d292798, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292799 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292799, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292868 q = 1) (hb : d294008 q = 1) : d295103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292868, d294008, d295103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292868, d294008, d295103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292869 q = 1) (hb : d294009 q = 1) : d295104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292869, d294009, d295104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292869, d294009, d295104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292870 q = 1) (hb : d294010 q = 1) : d295105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292870, d294010, d295105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292870, d294010, d295105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292912 q = 1) (hb : d294035 q = 1) : d295130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292912, d294035, d295130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292912, d294035, d295130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75806 (p : Pattern) (ha : d292915 p = 1) (hb : d294038 p = 1) : d295133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292889 q = 1) (hb : d293935 q = 1) : d295045 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292889, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75798 q ha hb
    | true =>
      simp only [d292889, d293935, d295045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292890 q = 1) (hb : d293936 q = 1) : d295046 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292890, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292890, d293936, d295046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292891 q = 1) (hb : d294014 q = 1) : d295109 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d292891, d294014, d295109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292891, d294014, d295109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292892 q = 1) (hb : d294015 q = 1) : d295110 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d292892, d294015, d295110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292892, d294015, d295110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292893 q = 1) (hb : d294016 q = 1) : d295111 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d292893, d294016, d295111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292893, d294016, d295111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292915 q = 1) (hb : d294038 q = 1) : d295133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d292915, d294038, d295133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292915, d294038, d295133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75807 (p : Pattern) (ha : d292921 p = 1) (hb : d294044 p = 1) : d295139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292835 q = 1) (hb : d293972 q = 1) : d295082 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292835, d293972, d295082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75786 q ha hb
    | true =>
      simp only [d292835, d293972, d295082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75787 q ha hb
  have h2 (q : Pattern) (ha : d292836 q = 1) (hb : d293973 q = 1) : d295083 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292836, d293973, d295083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292836, d293973, d295083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292837 q = 1) (hb : d293974 q = 1) : d295084 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292837, d293974, d295084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292837, d293974, d295084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292838 q = 1) (hb : d293975 q = 1) : d295085 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292838, d293975, d295085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292838, d293975, d295085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292845 q = 1) (hb : d293982 q = 1) : d295092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292845, d293982, d295092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75788 q ha hb
    | true =>
      simp only [d292845, d293982, d295092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75789 q ha hb
  have h6 (q : Pattern) (ha : d292846 q = 1) (hb : d293983 q = 1) : d295093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292846, d293983, d295093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292846, d293983, d295093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292847 q = 1) (hb : d293984 q = 1) : d295094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292847, d293984, d295094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292847, d293984, d295094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292872 q = 1) (hb : d294012 q = 1) : d295107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292872, d294012, d295107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75794 q ha hb
    | true =>
      simp only [d292872, d294012, d295107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75780 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d292812 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d292873 q = 1) (hb : d294013 q = 1) : d295108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292873, d294013, d295108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292873, d294013, d295108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d292895 q = 1) (hb : d294018 q = 1) : d295113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292895, d294018, d295113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75799 q ha hb
    | true =>
      simp only [d292895, d294018, d295113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d292896 q = 1) (hb : d294019 q = 1) : d295114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292896, d294019, d295114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292896, d294019, d295114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d292897 q = 1) (hb : d294020 q = 1) : d295115 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292897, d294020, d295115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292897, d294020, d295115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292898 q = 1) (hb : d294021 q = 1) : d295116 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292898, d294021, d295116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292898, d294021, d295116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d292899 q = 1) (hb : d294022 q = 1) : d295117 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292899, d294022, d295117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292899, d294022, d295117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d292903 q = 1) (hb : d294026 q = 1) : d295121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292903, d294026, d295121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75801 q ha hb
    | true =>
      simp only [d292903, d294026, d295121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75802 q ha hb
  have h17 (q : Pattern) (ha : d292904 q = 1) (hb : d294027 q = 1) : d295122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292904, d294027, d295122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292904, d294027, d295122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d292905 q = 1) (hb : d294028 q = 1) : d295123 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292905, d294028, d295123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d292905, d294028, d295123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d292906 q = 1) (hb : d294029 q = 1) : d295124 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292906, d294029, d295124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292906, d294029, d295124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d292909 q = 1) (hb : d294032 q = 1) : d295127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292909, d294032, d295127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75803 q ha hb
    | true =>
      simp only [d292909, d294032, d295127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75804 q ha hb
  have h21 (q : Pattern) (ha : d292910 q = 1) (hb : d294033 q = 1) : d295128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292910, d294033, d295128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292910, d294033, d295128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d292911 q = 1) (hb : d294034 q = 1) : d295129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292911, d294034, d295129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d292911, d294034, d295129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d292913 q = 1) (hb : d294036 q = 1) : d295131 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292913, d294036, d295131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75805 q ha hb
    | true =>
      simp only [d292913, d294036, d295131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75783 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d292822 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d292914 q = 1) (hb : d294037 q = 1) : d295132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292914, d294037, d295132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d292914, d294037, d295132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d292916 q = 1) (hb : d294039 q = 1) : d295134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292916, d294039, d295134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75806 q ha hb
    | true =>
      simp only [d292916, d294039, d295134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d292917 q = 1) (hb : d294040 q = 1) : d295135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292917, d294040, d295135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d292917, d294040, d295135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d292918 q = 1) (hb : d294041 q = 1) : d295136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292918, d294041, d295136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d292918, d294041, d295136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d292919 q = 1) (hb : d294042 q = 1) : d295137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292919, d294042, d295137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d292919, d294042, d295137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d292920 q = 1) (hb : d294043 q = 1) : d295138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292920, d294043, d295138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d292920, d294043, d295138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d292921 q = 1) (hb : d294044 q = 1) : d295139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292921, d294044, d295139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292921, d294044, d295139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro75808 (p : Pattern) (ha : d292928 p = 1) (hb : d294051 p = 1) : d295146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292812 q = 1) (hb : d293949 q = 1) : d295059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75780 q ha hb
    | true =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75781 q ha hb
  have h2 (q : Pattern) (ha : d292813 q = 1) (hb : d293950 q = 1) : d295060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292813, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292813, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292814 q = 1) (hb : d293951 q = 1) : d295061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292814, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292814, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292815 q = 1) (hb : d293952 q = 1) : d295062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292815, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292815, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292816 q = 1) (hb : d293953 q = 1) : d295063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292816, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292816, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292923 q = 1) (hb : d294046 q = 1) : d295141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292923, d294046, d295141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75781 q ha hb
    | true =>
      simp only [d292923, d294046, d295141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292924 q = 1) (hb : d294047 q = 1) : d295142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292924, d294047, d295142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292924, d294047, d295142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292925 q = 1) (hb : d294048 q = 1) : d295143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292925, d294048, d295143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292925, d294048, d295143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292926 q = 1) (hb : d294049 q = 1) : d295144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292926, d294049, d295144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292926, d294049, d295144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292927 q = 1) (hb : d294050 q = 1) : d295145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292927, d294050, d295145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292927, d294050, d295145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292928 q = 1) (hb : d294051 q = 1) : d295146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292928, d294051, d295146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292928, d294051, d295146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75809 (p : Pattern) (ha : d292934 p = 1) (hb : d294057 p = 1) : d295152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292923 q = 1) (hb : d294046 q = 1) : d295141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292923, d294046, d295141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75781 q ha hb
    | true =>
      simp only [d292923, d294046, d295141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292924 q = 1) (hb : d294047 q = 1) : d295142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292924, d294047, d295142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292924, d294047, d295142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292925 q = 1) (hb : d294048 q = 1) : d295143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292925, d294048, d295143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292925, d294048, d295143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292926 q = 1) (hb : d294049 q = 1) : d295144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292926, d294049, d295144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292926, d294049, d295144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292927 q = 1) (hb : d294050 q = 1) : d295145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292927, d294050, d295145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292927, d294050, d295145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292929 q = 1) (hb : d294052 q = 1) : d295147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292929, d294052, d295147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75784 q ha hb
    | true =>
      simp only [d292929, d294052, d295147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292930 q = 1) (hb : d294053 q = 1) : d295148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292930, d294053, d295148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292930, d294053, d295148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292931 q = 1) (hb : d294054 q = 1) : d295149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292931, d294054, d295149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292931, d294054, d295149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292932 q = 1) (hb : d294055 q = 1) : d295150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292932, d294055, d295150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292932, d294055, d295150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292933 q = 1) (hb : d294056 q = 1) : d295151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292933, d294056, d295151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292933, d294056, d295151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292934 q = 1) (hb : d294057 q = 1) : d295152 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292934, d294057, d295152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292934, d294057, d295152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75810 (p : Pattern) (ha : d292941 p = 1) (hb : d294064 p = 1) : d295159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292913 q = 1) (hb : d294036 q = 1) : d295131 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292913, d294036, d295131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75805 q ha hb
    | true =>
      simp only [d292913, d294036, d295131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75783 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292914 q = 1) (hb : d294037 q = 1) : d295132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292914, d294037, d295132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292914, d294037, d295132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d292916 q = 1) (hb : d294039 q = 1) : d295134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292916, d294039, d295134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75806 q ha hb
    | true =>
      simp only [d292916, d294039, d295134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292917 q = 1) (hb : d294040 q = 1) : d295135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292917, d294040, d295135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292917, d294040, d295135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d292918 q = 1) (hb : d294041 q = 1) : d295136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292918, d294041, d295136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292918, d294041, d295136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292939 q = 1) (hb : d294062 q = 1) : d295157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292939, d294062, d295157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292939, d294062, d295157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292940 q = 1) (hb : d294063 q = 1) : d295158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292940, d294063, d295158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292940, d294063, d295158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292941 q = 1) (hb : d294064 q = 1) : d295159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292941, d294064, d295159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292941, d294064, d295159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro75811 (p : Pattern) (ha : d292943 p = 1) (hb : d294066 p = 1) : d295161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292929 q = 1) (hb : d294052 q = 1) : d295147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292929, d294052, d295147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75784 q ha hb
    | true =>
      simp only [d292929, d294052, d295147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292930 q = 1) (hb : d294053 q = 1) : d295148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292930, d294053, d295148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292930, d294053, d295148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292931 q = 1) (hb : d294054 q = 1) : d295149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292931, d294054, d295149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292931, d294054, d295149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d292932 q = 1) (hb : d294055 q = 1) : d295150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292932, d294055, d295150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292932, d294055, d295150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292933 q = 1) (hb : d294056 q = 1) : d295151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292933, d294056, d295151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292933, d294056, d295151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292943 q = 1) (hb : d294066 q = 1) : d295161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292943, d294066, d295161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292943, d294066, d295161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75812 (p : Pattern) (ha : d292963 p = 1) (hb : d294078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d292952 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292953 q = 1) (hb : d293792 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292953, d293792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292953, d293792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75770 q ha hb
  have h3 (q : Pattern) (ha : d292759 q = 1) (hb : d293694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292759, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75770 q ha hb
    | true =>
      simp only [d292759, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d292954 q = 1) (hb : d293793 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292954, d293793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292954, d293793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292760 q = 1) (hb : d293695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292760, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292760, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d292955 q = 1) (hb : d293794 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292955, d293794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292955, d293794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292956 q = 1) (hb : d293795 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292956, d293795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292956, d293795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d292957 q = 1) (hb : d294072 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292957, d294072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292957, d294072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292958 q = 1) (hb : d294073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292958, d294073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292958, d294073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75772 q ha hb
  have h10 (q : Pattern) (ha : d292765 q = 1) (hb : d293899 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292765, d293899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75772 q ha hb
    | true =>
      simp only [d292765, d293899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d292959 q = 1) (hb : d294074 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292959, d294074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292959, d294074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d292766 q = 1) (hb : d293900 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292766, d293900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292766, d293900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d292960 q = 1) (hb : d294075 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292960, d294075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292960, d294075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292961 q = 1) (hb : d294076 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292961, d294076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292961, d294076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d292962 q = 1) (hb : d294077 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292962, d294077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292962, d294077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d292963 q = 1) (hb : d294078 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292963, d294078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292963, d294078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro75813 (p : Pattern) (ha : d292969 p = 1) (hb : d294089 p = 1) : d295168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292953 q = 1) (hb : d293792 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292953, d293792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292953, d293792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75770 q ha hb
  have h2 (q : Pattern) (ha : d292759 q = 1) (hb : d293694 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292759, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75770 q ha hb
    | true =>
      simp only [d292759, d293694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292954 q = 1) (hb : d293793 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292954, d293793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292954, d293793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292760 q = 1) (hb : d293695 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292760, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292760, d293695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292955 q = 1) (hb : d293794 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292955, d293794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292955, d293794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292956 q = 1) (hb : d293795 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292956, d293795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292956, d293795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292958 q = 1) (hb : d294079 q = 1) : d294951 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292958, d294079, d294951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292958, d294079, d294951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75771 q ha hb
  have h8 (q : Pattern) (ha : d292765 q = 1) (hb : d293890 q = 1) : d294873 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292765, d293890, d294873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75771 q ha hb
    | true =>
      simp only [d292765, d293890, d294873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292959 q = 1) (hb : d294080 q = 1) : d294952 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292959, d294080, d294952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292959, d294080, d294952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292766 q = 1) (hb : d293891 q = 1) : d294874 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292766, d293891, d294874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292766, d293891, d294874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d292960 q = 1) (hb : d294081 q = 1) : d294953 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292960, d294081, d294953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292960, d294081, d294953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d292961 q = 1) (hb : d294082 q = 1) : d294954 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292961, d294082, d294954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292961, d294082, d294954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d292962 q = 1) (hb : d294083 q = 1) : d294955 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292962, d294083, d294955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292962, d294083, d294955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292958 q = 1) (hb : d294073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292958, d294073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292958, d294073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75772 q ha hb
  have h15 (q : Pattern) (ha : d292765 q = 1) (hb : d293899 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292765, d293899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75772 q ha hb
    | true =>
      simp only [d292765, d293899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d292959 q = 1) (hb : d294074 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292959, d294074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d292959, d294074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d292766 q = 1) (hb : d293900 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292766, d293900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292766, d293900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d292960 q = 1) (hb : d294075 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292960, d294075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d292960, d294075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d292961 q = 1) (hb : d294076 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292961, d294076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d292961, d294076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d292967 q = 1) (hb : d294087 q = 1) : d294087 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d292968 q = 1) (hb : d294088 q = 1) : d295167 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292968, d294088, d295167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d292968, d294088, d295167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d292969 q = 1) (hb : d294089 q = 1) : d295168 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292969, d294089, d295168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292969, d294089, d295168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro75814 (p : Pattern) (ha : d292974 p = 1) (hb : d294099 p = 1) : d295172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292958 q = 1) (hb : d294093 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292958, d294093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292958, d294093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75791 q ha hb
  have h2 (q : Pattern) (ha : d292765 q = 1) (hb : d293994 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292765, d293994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75791 q ha hb
    | true =>
      simp only [d292765, d293994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292959 q = 1) (hb : d294094 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292959, d294094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292959, d294094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292766 q = 1) (hb : d293995 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292766, d293995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292766, d293995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292960 q = 1) (hb : d294095 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292960, d294095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292960, d294095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292961 q = 1) (hb : d294096 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292961, d294096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292961, d294096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292967 q = 1) (hb : d294087 q = 1) : d294087 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d292968 q = 1) (hb : d294097 q = 1) : d295167 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292968, d294097, d295167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292968, d294097, d295167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292973 q = 1) (hb : d294098 q = 1) : d294098 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d292974 q = 1) (hb : d294099 q = 1) : d295172 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292974, d294099, d295172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292974, d294099, d295172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75815 (p : Pattern) (ha : d292984 p = 1) (hb : d294109 p = 1) : d295172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292979 q = 1) (hb : d294079 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292979, d294079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292979, d294079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75775 q ha hb
  have h2 (q : Pattern) (ha : d292780 q = 1) (hb : d293890 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292780, d293890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75775 q ha hb
    | true =>
      simp only [d292780, d293890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292980 q = 1) (hb : d294080 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292980, d294080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292980, d294080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292781 q = 1) (hb : d293891 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292781, d293891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292781, d293891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292981 q = 1) (hb : d294081 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292981, d294081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292981, d294081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292982 q = 1) (hb : d294082 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292982, d294082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292982, d294082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292964 q = 1) (hb : d294104 q = 1) : d294084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292964, d294104, d294084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292964, d294104, d294084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
  have h8 (q : Pattern) (ha : d292772 q = 1) (hb : d293916 q = 1) : d293906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
    | true =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292965 q = 1) (hb : d294105 q = 1) : d294085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292965, d294105, d294085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292965, d294105, d294085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292773 q = 1) (hb : d293917 q = 1) : d293907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d292966 q = 1) (hb : d294106 q = 1) : d294086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292966, d294106, d294086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292966, d294106, d294086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d292967 q = 1) (hb : d294107 q = 1) : d294087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292967, d294107, d294087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292967, d294107, d294087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d292983 q = 1) (hb : d294108 q = 1) : d295167 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292983, d294108, d295167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292983, d294108, d295167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292973 q = 1) (hb : d294098 q = 1) : d294098 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d292984 q = 1) (hb : d294109 q = 1) : d295172 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292984, d294109, d295172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292984, d294109, d295172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75816 (p : Pattern) (ha : d292988 p = 1) (hb : d294114 p = 1) : d295177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292964 q = 1) (hb : d294104 q = 1) : d294084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292964, d294104, d294084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292964, d294104, d294084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
  have h2 (q : Pattern) (ha : d292772 q = 1) (hb : d293916 q = 1) : d293906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
    | true =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292965 q = 1) (hb : d294105 q = 1) : d294085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292965, d294105, d294085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292965, d294105, d294085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292773 q = 1) (hb : d293917 q = 1) : d293907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292966 q = 1) (hb : d294106 q = 1) : d294086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292966, d294106, d294086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292966, d294106, d294086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292967 q = 1) (hb : d294107 q = 1) : d294087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292967, d294107, d294087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292967, d294107, d294087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292973 q = 1) (hb : d294113 q = 1) : d294098 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292973, d294113, d294098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292973, d294113, d294098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d292988 q = 1) (hb : d294114 q = 1) : d295177 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d292988, d294114, d295177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292988, d294114, d295177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75817 (p : Pattern) (ha : d292994 p = 1) (hb : d294120 p = 1) : d295183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292970 q = 1) (hb : d294090 q = 1) : d295169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292970, d294090, d295169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75812 q ha hb
    | true =>
      simp only [d292970, d294090, d295169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75813 q ha hb
  have h2 (q : Pattern) (ha : d292971 q = 1) (hb : d294091 q = 1) : d295170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292971, d294091, d295170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292971, d294091, d295170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292972 q = 1) (hb : d294092 q = 1) : d295171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292972, d294092, d295171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292972, d294092, d295171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292975 q = 1) (hb : d294100 q = 1) : d295173 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292975, d294100, d295173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75813 q ha hb
    | true =>
      simp only [d292975, d294100, d295173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75814 q ha hb
  have h5 (q : Pattern) (ha : d292976 q = 1) (hb : d294101 q = 1) : d295174 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292976, d294101, d295174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292976, d294101, d295174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292977 q = 1) (hb : d294102 q = 1) : d295175 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292977, d294102, d295175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292977, d294102, d295175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292978 q = 1) (hb : d294103 q = 1) : d295176 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292978, d294103, d295176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292978, d294103, d295176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292985 q = 1) (hb : d294110 q = 1) : d295173 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292985, d294110, d295173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75813 q ha hb
    | true =>
      simp only [d292985, d294110, d295173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75815 q ha hb
  have h9 (q : Pattern) (ha : d292986 q = 1) (hb : d294111 q = 1) : d295174 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292986, d294111, d295174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292986, d294111, d295174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292987 q = 1) (hb : d294112 q = 1) : d295175 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292987, d294112, d295175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292987, d294112, d295175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292989 q = 1) (hb : d294115 q = 1) : d295178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292989, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75815 q ha hb
    | true =>
      simp only [d292989, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75816 q ha hb
  have h12 (q : Pattern) (ha : d292990 q = 1) (hb : d294116 q = 1) : d295179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292990, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292990, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d292991 q = 1) (hb : d294117 q = 1) : d295180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292991, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292991, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292992 q = 1) (hb : d294118 q = 1) : d295181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292992, d294118, d295181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292992, d294118, d295181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d292993 q = 1) (hb : d294119 q = 1) : d295182 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292993, d294119, d295182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292993, d294119, d295182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d292994 q = 1) (hb : d294120 q = 1) : d295183 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292994, d294120, d295183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292994, d294120, d295183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro75818 (p : Pattern) (ha : d292999 p = 1) (hb : d294125 p = 1) : d295188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292985 q = 1) (hb : d294110 q = 1) : d295173 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292985, d294110, d295173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75813 q ha hb
    | true =>
      simp only [d292985, d294110, d295173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75815 q ha hb
  have h2 (q : Pattern) (ha : d292986 q = 1) (hb : d294111 q = 1) : d295174 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292986, d294111, d295174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292986, d294111, d295174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292987 q = 1) (hb : d294112 q = 1) : d295175 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292987, d294112, d295175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292987, d294112, d295175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292989 q = 1) (hb : d294115 q = 1) : d295178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292989, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75815 q ha hb
    | true =>
      simp only [d292989, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75816 q ha hb
  have h5 (q : Pattern) (ha : d292990 q = 1) (hb : d294116 q = 1) : d295179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292990, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292990, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292991 q = 1) (hb : d294117 q = 1) : d295180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292991, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292991, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292992 q = 1) (hb : d294118 q = 1) : d295181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292992, d294118, d295181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292992, d294118, d295181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292997 q = 1) (hb : d294123 q = 1) : d295186 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292997, d294123, d295186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292997, d294123, d295186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292998 q = 1) (hb : d294124 q = 1) : d295187 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d292998, d294124, d295187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292998, d294124, d295187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292999 q = 1) (hb : d294125 q = 1) : d295188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d292999, d294125, d295188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292999, d294125, d295188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro75819 (p : Pattern) (ha : d293005 p = 1) (hb : d294131 p = 1) : d295194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292995 q = 1) (hb : d294121 q = 1) : d295184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d292995, d294121, d295184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75817 q ha hb
    | true =>
      simp only [d292995, d294121, d295184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d292996 q = 1) (hb : d294122 q = 1) : d295185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d292996, d294122, d295185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292996, d294122, d295185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293000 q = 1) (hb : d294126 q = 1) : d295189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293000, d294126, d295189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75818 q ha hb
    | true =>
      simp only [d293000, d294126, d295189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293001 q = 1) (hb : d294127 q = 1) : d295190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293001, d294127, d295190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293001, d294127, d295190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293002 q = 1) (hb : d294128 q = 1) : d295191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293002, d294128, d295191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293002, d294128, d295191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293003 q = 1) (hb : d294129 q = 1) : d295192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293003, d294129, d295192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293003, d294129, d295192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293004 q = 1) (hb : d294130 q = 1) : d295193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293004, d294130, d295193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293004, d294130, d295193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293005 q = 1) (hb : d294131 q = 1) : d295194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293005, d294131, d295194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293005, d294131, d295194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75820 (p : Pattern) (ha : d293007 p = 1) (hb : d294133 p = 1) : d295196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292989 q = 1) (hb : d294115 q = 1) : d295178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292989, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75815 q ha hb
    | true =>
      simp only [d292989, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75816 q ha hb
  have h2 (q : Pattern) (ha : d292990 q = 1) (hb : d294116 q = 1) : d295179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292990, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292990, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292991 q = 1) (hb : d294117 q = 1) : d295180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292991, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292991, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292997 q = 1) (hb : d294123 q = 1) : d295186 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292997, d294123, d295186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292997, d294123, d295186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293006 q = 1) (hb : d294132 q = 1) : d295195 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293006, d294132, d295195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293006, d294132, d295195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293007 q = 1) (hb : d294133 q = 1) : d295196 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293007, d294133, d295196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293007, d294133, d295196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75821 (p : Pattern) (ha : d293013 p = 1) (hb : d294139 p = 1) : d295202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293000 q = 1) (hb : d294126 q = 1) : d295189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293000, d294126, d295189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75818 q ha hb
    | true =>
      simp only [d293000, d294126, d295189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293001 q = 1) (hb : d294127 q = 1) : d295190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293001, d294127, d295190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293001, d294127, d295190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293008 q = 1) (hb : d294134 q = 1) : d295197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293008, d294134, d295197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75820 q ha hb
    | true =>
      simp only [d293008, d294134, d295197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293009 q = 1) (hb : d294135 q = 1) : d295198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293009, d294135, d295198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293009, d294135, d295198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293010 q = 1) (hb : d294136 q = 1) : d295199 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293010, d294136, d295199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293010, d294136, d295199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293011 q = 1) (hb : d294137 q = 1) : d295200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293011, d294137, d295200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293011, d294137, d295200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293012 q = 1) (hb : d294138 q = 1) : d295201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293012, d294138, d295201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293012, d294138, d295201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293013 q = 1) (hb : d294139 q = 1) : d295202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293013, d294139, d295202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293013, d294139, d295202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75822 (p : Pattern) (ha : d293026 p = 1) (hb : d294109 p = 1) : d295172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292979 q = 1) (hb : d294079 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292979, d294079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292979, d294079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75775 q ha hb
  have h2 (q : Pattern) (ha : d292780 q = 1) (hb : d293890 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292780, d293890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75775 q ha hb
    | true =>
      simp only [d292780, d293890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292980 q = 1) (hb : d294080 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292980, d294080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292980, d294080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292781 q = 1) (hb : d293891 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292781, d293891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292781, d293891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292981 q = 1) (hb : d294081 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292981, d294081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292981, d294081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292982 q = 1) (hb : d294082 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292982, d294082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292982, d294082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d292964 q = 1) (hb : d294104 q = 1) : d294084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292964, d294104, d294084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292964, d294104, d294084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
  have h8 (q : Pattern) (ha : d292772 q = 1) (hb : d293916 q = 1) : d293906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75774 q ha hb
    | true =>
      simp only [d292772, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d292965 q = 1) (hb : d294105 q = 1) : d294085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292965, d294105, d294085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292965, d294105, d294085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292773 q = 1) (hb : d293917 q = 1) : d293907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292773, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d292966 q = 1) (hb : d294106 q = 1) : d294086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d292966, d294106, d294086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292966, d294106, d294086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d292967 q = 1) (hb : d294107 q = 1) : d294087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d292967, d294107, d294087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292967, d294107, d294087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d292983 q = 1) (hb : d294108 q = 1) : d295167 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d292983, d294108, d295167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292983, d294108, d295167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293025 q = 1) (hb : d294098 q = 1) : d294098 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d293026 q = 1) (hb : d294109 q = 1) : d295172 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293026, d294109, d295172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293026, d294109, d295172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75823 (p : Pattern) (ha : d293027 p = 1) (hb : d294114 p = 1) : d295177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293021 q = 1) (hb : d294104 q = 1) : d294084 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293021, d294104, d294084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293021, d294104, d294084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75796 q ha hb
  have h2 (q : Pattern) (ha : d292876 q = 1) (hb : d293916 q = 1) : d293906 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d292876, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75796 q ha hb
    | true =>
      simp only [d292876, d293916, d293906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293022 q = 1) (hb : d294105 q = 1) : d294085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293022, d294105, d294085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293022, d294105, d294085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292877 q = 1) (hb : d293917 q = 1) : d293907 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d292877, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292877, d293917, d293907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293023 q = 1) (hb : d294106 q = 1) : d294086 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293023, d294106, d294086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293023, d294106, d294086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293024 q = 1) (hb : d294107 q = 1) : d294087 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293024, d294107, d294087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293024, d294107, d294087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293025 q = 1) (hb : d294113 q = 1) : d294098 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293025, d294113, d294098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293025, d294113, d294098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293027 q = 1) (hb : d294114 q = 1) : d295177 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293027, d294114, d295177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293027, d294114, d295177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75824 (p : Pattern) (ha : d293033 p = 1) (hb : d294125 p = 1) : d295188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292985 q = 1) (hb : d294110 q = 1) : d295173 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292985, d294110, d295173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75813 q ha hb
    | true =>
      simp only [d292985, d294110, d295173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75815 q ha hb
  have h2 (q : Pattern) (ha : d292986 q = 1) (hb : d294111 q = 1) : d295174 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292986, d294111, d295174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292986, d294111, d295174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292987 q = 1) (hb : d294112 q = 1) : d295175 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292987, d294112, d295175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292987, d294112, d295175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292989 q = 1) (hb : d294115 q = 1) : d295178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d292989, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75815 q ha hb
    | true =>
      simp only [d292989, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75816 q ha hb
  have h5 (q : Pattern) (ha : d292990 q = 1) (hb : d294116 q = 1) : d295179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d292990, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292990, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292991 q = 1) (hb : d294117 q = 1) : d295180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d292991, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292991, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292992 q = 1) (hb : d294118 q = 1) : d295181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d292992, d294118, d295181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292992, d294118, d295181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293028 q = 1) (hb : d294115 q = 1) : d295178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293028, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75822 q ha hb
    | true =>
      simp only [d293028, d294115, d295178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75823 q ha hb
  have h9 (q : Pattern) (ha : d293029 q = 1) (hb : d294116 q = 1) : d295179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293029, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293029, d294116, d295179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293030 q = 1) (hb : d294117 q = 1) : d295180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293030, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293030, d294117, d295180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293031 q = 1) (hb : d294123 q = 1) : d295186 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293031, d294123, d295186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293031, d294123, d295186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d293032 q = 1) (hb : d294124 q = 1) : d295187 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293032, d294124, d295187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293032, d294124, d295187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293033 q = 1) (hb : d294125 q = 1) : d295188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293033, d294125, d295188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d293033, d294125, d295188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro75825 (p : Pattern) (ha : d293039 p = 1) (hb : d294145 p = 1) : d295208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293034 q = 1) (hb : d294126 q = 1) : d295189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293034, d294126, d295189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75824 q ha hb
    | true =>
      simp only [d293034, d294126, d295189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293035 q = 1) (hb : d294127 q = 1) : d295190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293035, d294127, d295190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293035, d294127, d295190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293036 q = 1) (hb : d294142 q = 1) : d295205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293036, d294142, d295205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293036, d294142, d295205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293037 q = 1) (hb : d294143 q = 1) : d295206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293037, d294143, d295206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293037, d294143, d295206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293038 q = 1) (hb : d294144 q = 1) : d295207 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293038, d294144, d295207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293038, d294144, d295207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293039 q = 1) (hb : d294145 q = 1) : d295208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293039, d294145, d295208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293039, d294145, d295208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75826 (p : Pattern) (ha : d293045 p = 1) (hb : d294151 p = 1) : d295214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293014 q = 1) (hb : d294140 q = 1) : d295203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293014, d294140, d295203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75819 q ha hb
    | true =>
      simp only [d293014, d294140, d295203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75821 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293019 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293020 q = 1) (hb : d294141 q = 1) : d295204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293020, d294141, d295204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293020, d294141, d295204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d293040 q = 1) (hb : d294146 q = 1) : d295209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293040, d294146, d295209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75825 q ha hb
    | true =>
      simp only [d293040, d294146, d295209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293041 q = 1) (hb : d294147 q = 1) : d295210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293041, d294147, d295210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293041, d294147, d295210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293042 q = 1) (hb : d294148 q = 1) : d295211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293042, d294148, d295211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293042, d294148, d295211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293043 q = 1) (hb : d294149 q = 1) : d295212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293043, d294149, d295212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293043, d294149, d295212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293044 q = 1) (hb : d294150 q = 1) : d295213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293044, d294150, d295213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293044, d294150, d295213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293045 q = 1) (hb : d294151 q = 1) : d295214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293045, d294151, d295214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293045, d294151, d295214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro75827 (p : Pattern) (ha : d293018 p = 1) (hb : d294156 p = 1) : d295219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293008 q = 1) (hb : d294134 q = 1) : d295197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293008, d294134, d295197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75820 q ha hb
    | true =>
      simp only [d293008, d294134, d295197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293009 q = 1) (hb : d294135 q = 1) : d295198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293009, d294135, d295198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293009, d294135, d295198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293015 q = 1) (hb : d294153 q = 1) : d295216 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293015, d294153, d295216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293015, d294153, d295216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293016 q = 1) (hb : d294154 q = 1) : d295217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293016, d294154, d295217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293016, d294154, d295217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293017 q = 1) (hb : d294155 q = 1) : d295218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293017, d294155, d295218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293017, d294155, d295218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293018 q = 1) (hb : d294156 q = 1) : d295219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293018, d294156, d295219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293018, d294156, d295219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75828 (p : Pattern) (ha : d293052 p = 1) (hb : d294162 p = 1) : d295225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293047 q = 1) (hb : d294157 q = 1) : d295220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293047, d294157, d295220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75827 q ha hb
    | true =>
      simp only [d293047, d294157, d295220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293048 q = 1) (hb : d294158 q = 1) : d295221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293048, d294158, d295221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293048, d294158, d295221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293049 q = 1) (hb : d294159 q = 1) : d295222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293049, d294159, d295222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293049, d294159, d295222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293050 q = 1) (hb : d294160 q = 1) : d295223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293050, d294160, d295223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293050, d294160, d295223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293051 q = 1) (hb : d294161 q = 1) : d295224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293051, d294161, d295224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293051, d294161, d295224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293052 q = 1) (hb : d294162 q = 1) : d295225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293052, d294162, d295225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293052, d294162, d295225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75829 (p : Pattern) (ha : d293058 p = 1) (hb : d294168 p = 1) : d295231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292818 q = 1) (hb : d293955 q = 1) : d295065 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292818, d293955, d295065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292818, d293955, d295065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75782 q ha hb
  have h2 (q : Pattern) (ha : d292819 q = 1) (hb : d293956 q = 1) : d295066 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292819, d293956, d295066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292819, d293956, d295066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d292828 q = 1) (hb : d293965 q = 1) : d295075 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292828, d293965, d295075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75782 q ha hb
    | true =>
      simp only [d292828, d293965, d295075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75785 q ha hb
  have h4 (q : Pattern) (ha : d292829 q = 1) (hb : d293966 q = 1) : d295076 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292829, d293966, d295076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292829, d293966, d295076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d292830 q = 1) (hb : d293967 q = 1) : d295077 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292830, d293967, d295077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d292830, d293967, d295077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292922 q = 1) (hb : d294045 q = 1) : d295140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292922, d294045, d295140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75800 q ha hb
    | true =>
      simp only [d292922, d294045, d295140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75807 q ha hb
  have h7 (q : Pattern) (ha : d292935 q = 1) (hb : d294058 q = 1) : d295153 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292935, d294058, d295153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75808 q ha hb
    | true =>
      simp only [d292935, d294058, d295153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75809 q ha hb
  have h8 (q : Pattern) (ha : d292936 q = 1) (hb : d294059 q = 1) : d295154 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292936, d294059, d295154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292936, d294059, d295154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292937 q = 1) (hb : d294060 q = 1) : d295155 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292937, d294060, d295155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292937, d294060, d295155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d292938 q = 1) (hb : d294061 q = 1) : d295156 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292938, d294061, d295156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292938, d294061, d295156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d292942 q = 1) (hb : d294065 q = 1) : d295160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292942, d294065, d295160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292942, d294065, d295160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75810 q ha hb
  have h12 (q : Pattern) (ha : d292944 q = 1) (hb : d294067 q = 1) : d295162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292944, d294067, d295162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292944, d294067, d295162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75811 q ha hb
  have h13 (q : Pattern) (ha : d292945 q = 1) (hb : d294068 q = 1) : d295163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292945, d294068, d295163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d292945, d294068, d295163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d292946 q = 1) (hb : d294069 q = 1) : d295164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292946, d294069, d295164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292946, d294069, d295164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d292947 q = 1) (hb : d294070 q = 1) : d295165 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292947, d294070, d295165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d292947, d294070, d295165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d292948 q = 1) (hb : d294071 q = 1) : d295166 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292948, d294071, d295166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292948, d294071, d295166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d293046 q = 1) (hb : d294152 q = 1) : d295215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293046, d294152, d295215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293046, d294152, d295215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75826 q ha hb
  have h18 (q : Pattern) (ha : d293053 q = 1) (hb : d294163 q = 1) : d295226 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293053, d294163, d295226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293053, d294163, d295226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75828 q ha hb
  have h19 (q : Pattern) (ha : d293054 q = 1) (hb : d294164 q = 1) : d295227 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293054, d294164, d295227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d293054, d294164, d295227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d293055 q = 1) (hb : d294165 q = 1) : d295228 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293055, d294165, d295228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d293055, d294165, d295228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d293056 q = 1) (hb : d294166 q = 1) : d295229 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d293056, d294166, d295229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d293056, d294166, d295229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d293057 q = 1) (hb : d294167 q = 1) : d295230 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d293057, d294167, d295230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d293057, d294167, d295230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d293058 q = 1) (hb : d294168 q = 1) : d295231 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d293058, d294168, d295231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d293058, d294168, d295231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro75830 (p : Pattern) (ha : d293064 p = 1) (hb : d294174 p = 1) : d295237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293059 q = 1) (hb : d294169 q = 1) : d295232 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d293059, d294169, d295232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293059, d294169, d295232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75829 q ha hb
  have h2 (q : Pattern) (ha : d293060 q = 1) (hb : d294170 q = 1) : d295233 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d293060, d294170, d295233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293060, d294170, d295233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293061 q = 1) (hb : d294171 q = 1) : d295234 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d293061, d294171, d295234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293061, d294171, d295234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293062 q = 1) (hb : d294172 q = 1) : d295235 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d293062, d294172, d295235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293062, d294172, d295235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293063 q = 1) (hb : d294173 q = 1) : d295236 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d293063, d294173, d295236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293063, d294173, d295236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293064 q = 1) (hb : d294174 q = 1) : d295237 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d293064, d294174, d295237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293064, d294174, d295237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75831 (p : Pattern) (ha : d293070 p = 1) (hb : d294179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32688 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32688, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75082 q ha hb
    | true =>
      simp only [d32688, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32689 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32689, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32689, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32690 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32691 q = 1) (hb : d293069 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32691, d293069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32691, d293069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32692 q = 1) (hb : d293070 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32692, d293070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32692, d293070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d293070 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d293070 q = 1) (hb : d294179 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d294179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d294179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro75832 (p : Pattern) (ha : d293083 p = 1) (hb : d294194 p = 1) : d295243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156197 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d293073 q = 1) (hb : d294182 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293074 q = 1) (hb : d294183 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d293075 q = 1) (hb : d294184 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293075, d294184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293075, d294184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293081 q = 1) (hb : d294192 q = 1) : d294192 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d293082 q = 1) (hb : d294193 q = 1) : d295242 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293082, d294193, d295242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293082, d294193, d295242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293083 q = 1) (hb : d294194 q = 1) : d295243 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293083, d294194, d295243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293083, d294194, d295243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro75833 (p : Pattern) (ha : d293077 p = 1) (hb : d294198 p = 1) : d294188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d32701 q = 1) : d32701 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d32722 q = 1) (hb : d53337 q = 1) : d32702 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32722, d53337, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d32722, d53337, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15103 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32723 q = 1) (hb : d53338 q = 1) : d32703 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32723, d53338, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32723, d53338, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53338 q = 1) (hb : d294195 q = 1) : d294185 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d294195, d294185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d294195, d294185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2047 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15103 q ha hb
    | true =>
      simp only [d2047, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2048, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30103 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d293076 q = 1) (hb : d294196 q = 1) : d294186 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d293076, d294196, d294186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293076, d294196, d294186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d293077 q = 1) (hb : d294197 q = 1) : d294187 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d293077, d294197, d294187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d293077, d294197, d294187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d293077 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d293077 q = 1) (hb : d294198 q = 1) : d294188 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d294198, d294188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d294198, d294188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro75834 (p : Pattern) (ha : d293085 p = 1) (hb : d294205 p = 1) : d295244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293073 q = 1) (hb : d294182 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293074 q = 1) (hb : d294183 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293078 q = 1) (hb : d294199 q = 1) : d294189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
    | true =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293079 q = 1) (hb : d294200 q = 1) : d294190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293080 q = 1) (hb : d294201 q = 1) : d294191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293080, d294201, d294191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293080, d294201, d294191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293081 q = 1) (hb : d294202 q = 1) : d294192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293081, d294202, d294192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293081, d294202, d294192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293082 q = 1) (hb : d294203 q = 1) : d295242 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293082, d294203, d295242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293082, d294203, d295242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293084 q = 1) (hb : d294204 q = 1) : d294204 q = 1 := by
    exact hb
  have h11 (q : Pattern) (ha : d293085 q = 1) (hb : d294205 q = 1) : d295244 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293085, d294205, d295244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293085, d294205, d295244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75835 (p : Pattern) (ha : d293089 p = 1) (hb : d294210 p = 1) : d295248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293078 q = 1) (hb : d294199 q = 1) : d294189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
    | true =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293079 q = 1) (hb : d294200 q = 1) : d294190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293080 q = 1) (hb : d294201 q = 1) : d294191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293080, d294201, d294191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293080, d294201, d294191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293081 q = 1) (hb : d294202 q = 1) : d294192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293081, d294202, d294192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293081, d294202, d294192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293084 q = 1) (hb : d294209 q = 1) : d294204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293084, d294209, d294204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293084, d294209, d294204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293089 q = 1) (hb : d294210 q = 1) : d295248 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293089, d294210, d295248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293089, d294210, d295248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75836 (p : Pattern) (ha : d293096 p = 1) (hb : d294217 p = 1) : d295255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293086 q = 1) (hb : d294206 q = 1) : d295245 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293086, d294206, d295245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75832 q ha hb
    | true =>
      simp only [d293086, d294206, d295245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75834 q ha hb
  have h2 (q : Pattern) (ha : d293087 q = 1) (hb : d294207 q = 1) : d295246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293087, d294207, d295246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293087, d294207, d295246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293088 q = 1) (hb : d294208 q = 1) : d295247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293088, d294208, d295247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293088, d294208, d295247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293090 q = 1) (hb : d294211 q = 1) : d295249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293090, d294211, d295249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75834 q ha hb
    | true =>
      simp only [d293090, d294211, d295249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75835 q ha hb
  have h5 (q : Pattern) (ha : d293091 q = 1) (hb : d294212 q = 1) : d295250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293091, d294212, d295250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293091, d294212, d295250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293092 q = 1) (hb : d294213 q = 1) : d295251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293092, d294213, d295251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293092, d294213, d295251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293093 q = 1) (hb : d294214 q = 1) : d295252 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293093, d294214, d295252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293093, d294214, d295252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293094 q = 1) (hb : d294215 q = 1) : d295253 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293094, d294215, d295253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293094, d294215, d295253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293095 q = 1) (hb : d294216 q = 1) : d295254 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293095, d294216, d295254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293095, d294216, d295254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293096 q = 1) (hb : d294217 q = 1) : d295255 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293096, d294217, d295255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293096, d294217, d295255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro75837 (p : Pattern) (ha : d293100 p = 1) (hb : d294221 p = 1) : d295259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293090 q = 1) (hb : d294211 q = 1) : d295249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293090, d294211, d295249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75834 q ha hb
    | true =>
      simp only [d293090, d294211, d295249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75835 q ha hb
  have h2 (q : Pattern) (ha : d293091 q = 1) (hb : d294212 q = 1) : d295250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293091, d294212, d295250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293091, d294212, d295250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293092 q = 1) (hb : d294213 q = 1) : d295251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293092, d294213, d295251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293092, d294213, d295251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293094 q = 1) (hb : d294215 q = 1) : d295253 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293094, d294215, d295253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293094, d294215, d295253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293099 q = 1) (hb : d294220 q = 1) : d295258 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293099, d294220, d295258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293099, d294220, d295258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293100 q = 1) (hb : d294221 q = 1) : d295259 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293100, d294221, d295259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293100, d294221, d295259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75838 (p : Pattern) (ha : d293106 p = 1) (hb : d294227 p = 1) : d295265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293097 q = 1) (hb : d294218 q = 1) : d295256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75836 q ha hb
    | true =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293098 q = 1) (hb : d294219 q = 1) : d295257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293103 q = 1) (hb : d294224 q = 1) : d295262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293104 q = 1) (hb : d294225 q = 1) : d295263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293104, d294225, d295263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293104, d294225, d295263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293105 q = 1) (hb : d294226 q = 1) : d295264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293105, d294226, d295264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293105, d294226, d295264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293106 q = 1) (hb : d294227 q = 1) : d295265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293106, d294227, d295265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293106, d294227, d295265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75839 (p : Pattern) (ha : d293110 p = 1) (hb : d294231 p = 1) : d295269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293107 q = 1) (hb : d294228 q = 1) : d295266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293108 q = 1) (hb : d294229 q = 1) : d295267 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293108, d294229, d295267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293108, d294229, d295267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293109 q = 1) (hb : d294230 q = 1) : d295268 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293109, d294230, d295268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293109, d294230, d295268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293110 q = 1) (hb : d294231 q = 1) : d295269 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293110, d294231, d295269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293110, d294231, d295269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75840 (p : Pattern) (ha : d293116 p = 1) (hb : d294237 p = 1) : d295275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293111 q = 1) (hb : d294232 q = 1) : d295270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75838 q ha hb
    | true =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75839 q ha hb
  have h2 (q : Pattern) (ha : d293112 q = 1) (hb : d294233 q = 1) : d295271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293112, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293112, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293113 q = 1) (hb : d294234 q = 1) : d295272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293113, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293113, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293114 q = 1) (hb : d294235 q = 1) : d295273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293114, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293114, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293115 q = 1) (hb : d294236 q = 1) : d295274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293115, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293115, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293116 q = 1) (hb : d294237 q = 1) : d295275 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293116, d294237, d295275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293116, d294237, d295275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75841 (p : Pattern) (ha : d293119 p = 1) (hb : d294240 p = 1) : d295278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293097 q = 1) (hb : d294218 q = 1) : d295256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75836 q ha hb
    | true =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293098 q = 1) (hb : d294219 q = 1) : d295257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293103 q = 1) (hb : d294224 q = 1) : d295262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293104 q = 1) (hb : d294225 q = 1) : d295263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293104, d294225, d295263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293104, d294225, d295263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293105 q = 1) (hb : d294226 q = 1) : d295264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293105, d294226, d295264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293105, d294226, d295264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293119 q = 1) (hb : d294240 q = 1) : d295278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293119, d294240, d295278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293119, d294240, d295278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75842 (p : Pattern) (ha : d293120 p = 1) (hb : d294241 p = 1) : d295279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293107 q = 1) (hb : d294228 q = 1) : d295266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293108 q = 1) (hb : d294229 q = 1) : d295267 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293108, d294229, d295267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293108, d294229, d295267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293109 q = 1) (hb : d294230 q = 1) : d295268 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293109, d294230, d295268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293109, d294230, d295268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293120 q = 1) (hb : d294241 q = 1) : d295279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293120, d294241, d295279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293120, d294241, d295279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75843 (p : Pattern) (ha : d293126 p = 1) (hb : d294247 p = 1) : d295285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293111 q = 1) (hb : d294232 q = 1) : d295270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75838 q ha hb
    | true =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75839 q ha hb
  have h2 (q : Pattern) (ha : d293112 q = 1) (hb : d294233 q = 1) : d295271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293112, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293112, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293113 q = 1) (hb : d294234 q = 1) : d295272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293113, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293113, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293114 q = 1) (hb : d294235 q = 1) : d295273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293114, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293114, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293115 q = 1) (hb : d294236 q = 1) : d295274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293115, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293115, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293121 q = 1) (hb : d294242 q = 1) : d295280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293121, d294242, d295280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75841 q ha hb
    | true =>
      simp only [d293121, d294242, d295280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75842 q ha hb
  have h7 (q : Pattern) (ha : d293122 q = 1) (hb : d294243 q = 1) : d295281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293122, d294243, d295281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293122, d294243, d295281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293123 q = 1) (hb : d294244 q = 1) : d295282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293123, d294244, d295282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293123, d294244, d295282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293124 q = 1) (hb : d294245 q = 1) : d295283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293124, d294245, d295283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293124, d294245, d295283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293125 q = 1) (hb : d294246 q = 1) : d295284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293125, d294246, d295284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293125, d294246, d295284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293126 q = 1) (hb : d294247 q = 1) : d295285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293126, d294247, d295285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293126, d294247, d295285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75844 (p : Pattern) (ha : d293131 p = 1) (hb : d294252 p = 1) : d295290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293097 q = 1) (hb : d294218 q = 1) : d295256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75836 q ha hb
    | true =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293098 q = 1) (hb : d294219 q = 1) : d295257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293103 q = 1) (hb : d294224 q = 1) : d295262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293104 q = 1) (hb : d294225 q = 1) : d295263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293104, d294225, d295263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293104, d294225, d295263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293130 q = 1) (hb : d294251 q = 1) : d295289 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293130, d294251, d295289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293130, d294251, d295289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293131 q = 1) (hb : d294252 q = 1) : d295290 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293131, d294252, d295290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293131, d294252, d295290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75845 (p : Pattern) (ha : d293133 p = 1) (hb : d294254 p = 1) : d295292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293107 q = 1) (hb : d294228 q = 1) : d295266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293108 q = 1) (hb : d294229 q = 1) : d295267 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293108, d294229, d295267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293108, d294229, d295267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293132 q = 1) (hb : d294253 q = 1) : d295291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293132, d294253, d295291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293132, d294253, d295291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293133 q = 1) (hb : d294254 q = 1) : d295292 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293133, d294254, d295292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293133, d294254, d295292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75846 (p : Pattern) (ha : d293140 p = 1) (hb : d294261 p = 1) : d295299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293097 q = 1) (hb : d294218 q = 1) : d295256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75836 q ha hb
    | true =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293098 q = 1) (hb : d294219 q = 1) : d295257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293103 q = 1) (hb : d294224 q = 1) : d295262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293138 q = 1) (hb : d294259 q = 1) : d295297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293138, d294259, d295297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293138, d294259, d295297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293139 q = 1) (hb : d294260 q = 1) : d295298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293139, d294260, d295298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293139, d294260, d295298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293140 q = 1) (hb : d294261 q = 1) : d295299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293140, d294261, d295299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293140, d294261, d295299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75847 (p : Pattern) (ha : d293143 p = 1) (hb : d294264 p = 1) : d295302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293107 q = 1) (hb : d294228 q = 1) : d295266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293141 q = 1) (hb : d294262 q = 1) : d295300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293141, d294262, d295300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293141, d294262, d295300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293142 q = 1) (hb : d294263 q = 1) : d295301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293142, d294263, d295301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293142, d294263, d295301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293143 q = 1) (hb : d294264 q = 1) : d295302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293143, d294264, d295302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293143, d294264, d295302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75848 (p : Pattern) (ha : d293085 p = 1) (hb : d294272 p = 1) : d295244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293073 q = 1) (hb : d294182 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293074 q = 1) (hb : d294183 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293081 q = 1) (hb : d294192 q = 1) : d294192 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d293082 q = 1) (hb : d294193 q = 1) : d295242 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293082, d294193, d295242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293082, d294193, d295242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293084 q = 1) (hb : d294204 q = 1) : d294204 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d293085 q = 1) (hb : d294272 q = 1) : d295244 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293085, d294272, d295244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293085, d294272, d295244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75849 (p : Pattern) (ha : d293147 p = 1) (hb : d294268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156287 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156197 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d293073 q = 1) (hb : d294182 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293074 q = 1) (hb : d294183 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d293075 q = 1) (hb : d294184 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293075, d294184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293075, d294184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293147 q = 1) (hb : d294268 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293147, d294268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293147, d294268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75850 (p : Pattern) (ha : d293153 p = 1) (hb : d294278 p = 1) : d295311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293148 q = 1) (hb : d294269 q = 1) : d295306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293148, d294269, d295306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75849 q ha hb
    | true =>
      simp only [d293148, d294269, d295306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75832 q ha hb
  have h2 (q : Pattern) (ha : d293149 q = 1) (hb : d294270 q = 1) : d295307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293149, d294270, d295307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293149, d294270, d295307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293150 q = 1) (hb : d294271 q = 1) : d295308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293150, d294271, d295308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293150, d294271, d295308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293086 q = 1) (hb : d294273 q = 1) : d295245 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293086, d294273, d295245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75832 q ha hb
    | true =>
      simp only [d293086, d294273, d295245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75848 q ha hb
  have h5 (q : Pattern) (ha : d293087 q = 1) (hb : d294274 q = 1) : d295246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293087, d294274, d295246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293087, d294274, d295246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293088 q = 1) (hb : d294275 q = 1) : d295247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293088, d294275, d295247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293088, d294275, d295247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293151 q = 1) (hb : d294276 q = 1) : d295309 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293151, d294276, d295309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293151, d294276, d295309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293086 q = 1) (hb : d294206 q = 1) : d295245 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293086, d294206, d295245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75832 q ha hb
    | true =>
      simp only [d293086, d294206, d295245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75834 q ha hb
  have h9 (q : Pattern) (ha : d293087 q = 1) (hb : d294207 q = 1) : d295246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293087, d294207, d295246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293087, d294207, d295246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293088 q = 1) (hb : d294208 q = 1) : d295247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293088, d294208, d295247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293088, d294208, d295247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293090 q = 1) (hb : d294211 q = 1) : d295249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293090, d294211, d295249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75834 q ha hb
    | true =>
      simp only [d293090, d294211, d295249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75835 q ha hb
  have h12 (q : Pattern) (ha : d293091 q = 1) (hb : d294212 q = 1) : d295250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293091, d294212, d295250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293091, d294212, d295250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293092 q = 1) (hb : d294213 q = 1) : d295251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293092, d294213, d295251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293092, d294213, d295251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293093 q = 1) (hb : d294214 q = 1) : d295252 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293093, d294214, d295252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293093, d294214, d295252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d293152 q = 1) (hb : d294277 q = 1) : d295310 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293152, d294277, d295310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293152, d294277, d295310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293153 q = 1) (hb : d294278 q = 1) : d295311 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293153, d294278, d295311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d293153, d294278, d295311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro75851 (p : Pattern) (ha : d293159 p = 1) (hb : d294284 p = 1) : d295317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293154 q = 1) (hb : d294279 q = 1) : d295312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293154, d294279, d295312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75850 q ha hb
    | true =>
      simp only [d293154, d294279, d295312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293155 q = 1) (hb : d294280 q = 1) : d295313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293155, d294280, d295313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293155, d294280, d295313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293097 q = 1) (hb : d294218 q = 1) : d295256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75836 q ha hb
    | true =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293098 q = 1) (hb : d294219 q = 1) : d295257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293156 q = 1) (hb : d294281 q = 1) : d295314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293156, d294281, d295314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293156, d294281, d295314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293157 q = 1) (hb : d294282 q = 1) : d295315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293157, d294282, d295315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293157, d294282, d295315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293158 q = 1) (hb : d294283 q = 1) : d295316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293158, d294283, d295316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293158, d294283, d295316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293159 q = 1) (hb : d294284 q = 1) : d295317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293159, d294284, d295317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293159, d294284, d295317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75852 (p : Pattern) (ha : d156218 p = 1) (hb : d207150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d69323 q = 1) (hb : d207147 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d207147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d207147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d30103 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156217 q = 1) (hb : d207148 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d156217, d207148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156217, d207148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d156218 q = 1) (hb : d207149 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d156218, d207149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156218, d207149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d156218 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d156218 q = 1) (hb : d207150 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d207150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro75853 (p : Pattern) (ha : d156224 p = 1) (hb : d207156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156219 q = 1) (hb : d207151 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156219, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75852 q ha hb
    | true =>
      simp only [d156219, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156220 q = 1) (hb : d207152 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156220, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156220, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156221 q = 1) (hb : d207153 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156221, d207153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156221, d207153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156222 q = 1) (hb : d207154 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156222, d207154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156222, d207154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156223 q = 1) (hb : d207155 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156223, d207155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156223, d207155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156224 q = 1) (hb : d207156 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156224, d207156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156224, d207156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75854 (p : Pattern) (ha : d293162 p = 1) (hb : d294287 p = 1) : d295320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293073 q = 1) (hb : d294182 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293073, d294182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293074 q = 1) (hb : d294183 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293074, d294183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293078 q = 1) (hb : d294199 q = 1) : d294189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
    | true =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293079 q = 1) (hb : d294200 q = 1) : d294190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293080 q = 1) (hb : d294201 q = 1) : d294191 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293080, d294201, d294191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293080, d294201, d294191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293081 q = 1) (hb : d294202 q = 1) : d294192 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293081, d294202, d294192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293081, d294202, d294192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293082 q = 1) (hb : d294203 q = 1) : d295242 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293082, d294203, d295242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293082, d294203, d295242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d156223 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d293162 q = 1) (hb : d294287 q = 1) : d295320 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293162, d294287, d295320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293162, d294287, d295320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro75855 (p : Pattern) (ha : d293168 p = 1) (hb : d294293 p = 1) : d295326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293086 q = 1) (hb : d294206 q = 1) : d295245 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293086, d294206, d295245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75832 q ha hb
    | true =>
      simp only [d293086, d294206, d295245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75834 q ha hb
  have h2 (q : Pattern) (ha : d293087 q = 1) (hb : d294207 q = 1) : d295246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293087, d294207, d295246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293087, d294207, d295246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293088 q = 1) (hb : d294208 q = 1) : d295247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293088, d294208, d295247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293088, d294208, d295247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293090 q = 1) (hb : d294211 q = 1) : d295249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293090, d294211, d295249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75834 q ha hb
    | true =>
      simp only [d293090, d294211, d295249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75835 q ha hb
  have h5 (q : Pattern) (ha : d293091 q = 1) (hb : d294212 q = 1) : d295250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293091, d294212, d295250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293091, d294212, d295250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293092 q = 1) (hb : d294213 q = 1) : d295251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293092, d294213, d295251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293092, d294213, d295251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293093 q = 1) (hb : d294214 q = 1) : d295252 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293093, d294214, d295252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293093, d294214, d295252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293163 q = 1) (hb : d294288 q = 1) : d295321 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293163, d294288, d295321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75854 q ha hb
    | true =>
      simp only [d293163, d294288, d295321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75853 q ha hb
  have h9 (q : Pattern) (ha : d293164 q = 1) (hb : d294289 q = 1) : d295322 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293164, d294289, d295322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293164, d294289, d295322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293165 q = 1) (hb : d294290 q = 1) : d295323 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293165, d294290, d295323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293165, d294290, d295323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293166 q = 1) (hb : d294291 q = 1) : d295324 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293166, d294291, d295324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293166, d294291, d295324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d293167 q = 1) (hb : d294292 q = 1) : d295325 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293167, d294292, d295325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293167, d294292, d295325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293168 q = 1) (hb : d294293 q = 1) : d295326 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293168, d294293, d295326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d293168, d294293, d295326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro75856 (p : Pattern) (ha : d293174 p = 1) (hb : d294299 p = 1) : d295332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293169 q = 1) (hb : d294294 q = 1) : d295327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293169, d294294, d295327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75855 q ha hb
    | true =>
      simp only [d293169, d294294, d295327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293170 q = 1) (hb : d294295 q = 1) : d295328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293170, d294295, d295328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293170, d294295, d295328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293171 q = 1) (hb : d294296 q = 1) : d295329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293171, d294296, d295329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293171, d294296, d295329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293172 q = 1) (hb : d294297 q = 1) : d295330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293172, d294297, d295330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293172, d294297, d295330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293173 q = 1) (hb : d294298 q = 1) : d295331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293173, d294298, d295331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293173, d294298, d295331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293174 q = 1) (hb : d294299 q = 1) : d295332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293174, d294299, d295332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293174, d294299, d295332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75857 (p : Pattern) (ha : d293180 p = 1) (hb : d294305 p = 1) : d295338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293134 q = 1) (hb : d294255 q = 1) : d295293 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293134, d294255, d295293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75844 q ha hb
    | true =>
      simp only [d293134, d294255, d295293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75845 q ha hb
  have h2 (q : Pattern) (ha : d293135 q = 1) (hb : d294256 q = 1) : d295294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293135, d294256, d295294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293135, d294256, d295294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293136 q = 1) (hb : d294257 q = 1) : d295295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293136, d294257, d295295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293136, d294257, d295295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293137 q = 1) (hb : d294258 q = 1) : d295296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293137, d294258, d295296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293137, d294258, d295296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293144 q = 1) (hb : d294265 q = 1) : d295303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293144, d294265, d295303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75846 q ha hb
    | true =>
      simp only [d293144, d294265, d295303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75847 q ha hb
  have h6 (q : Pattern) (ha : d293145 q = 1) (hb : d294266 q = 1) : d295304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293145, d294266, d295304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293145, d294266, d295304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293146 q = 1) (hb : d294267 q = 1) : d295305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293146, d294267, d295305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293146, d294267, d295305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293160 q = 1) (hb : d294285 q = 1) : d295318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293160, d294285, d295318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75851 q ha hb
    | true =>
      simp only [d293160, d294285, d295318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75838 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d293111 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d293161 q = 1) (hb : d294286 q = 1) : d295319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293161, d294286, d295319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293161, d294286, d295319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d293175 q = 1) (hb : d294300 q = 1) : d295333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293175, d294300, d295333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75856 q ha hb
    | true =>
      simp only [d293175, d294300, d295333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d293176 q = 1) (hb : d294301 q = 1) : d295334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293176, d294301, d295334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293176, d294301, d295334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d293177 q = 1) (hb : d294302 q = 1) : d295335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293177, d294302, d295335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293177, d294302, d295335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293178 q = 1) (hb : d294303 q = 1) : d295336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293178, d294303, d295336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293178, d294303, d295336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d293179 q = 1) (hb : d294304 q = 1) : d295337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293179, d294304, d295337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293179, d294304, d295337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293180 q = 1) (hb : d294305 q = 1) : d295338 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293180, d294305, d295338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293180, d294305, d295338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro75858 (p : Pattern) (ha : d293181 p = 1) (hb : d294306 p = 1) : d295339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293097 q = 1) (hb : d294218 q = 1) : d295256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75836 q ha hb
    | true =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293098 q = 1) (hb : d294219 q = 1) : d295257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293103 q = 1) (hb : d294224 q = 1) : d295262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293104 q = 1) (hb : d294225 q = 1) : d295263 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293104, d294225, d295263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293104, d294225, d295263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293130 q = 1) (hb : d294251 q = 1) : d295289 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293130, d294251, d295289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293130, d294251, d295289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293181 q = 1) (hb : d294306 q = 1) : d295339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293181, d294306, d295339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293181, d294306, d295339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75859 (p : Pattern) (ha : d293182 p = 1) (hb : d294307 p = 1) : d295340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293107 q = 1) (hb : d294228 q = 1) : d295266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293108 q = 1) (hb : d294229 q = 1) : d295267 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293108, d294229, d295267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293108, d294229, d295267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293132 q = 1) (hb : d294253 q = 1) : d295291 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293132, d294253, d295291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293132, d294253, d295291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293182 q = 1) (hb : d294307 q = 1) : d295340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293182, d294307, d295340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293182, d294307, d295340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75860 (p : Pattern) (ha : d293187 p = 1) (hb : d294312 p = 1) : d295345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293097 q = 1) (hb : d294218 q = 1) : d295256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75836 q ha hb
    | true =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293098 q = 1) (hb : d294219 q = 1) : d295257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293103 q = 1) (hb : d294224 q = 1) : d295262 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293103, d294224, d295262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293138 q = 1) (hb : d294259 q = 1) : d295297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293138, d294259, d295297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293138, d294259, d295297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293139 q = 1) (hb : d294260 q = 1) : d295298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293139, d294260, d295298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293139, d294260, d295298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293187 q = 1) (hb : d294312 q = 1) : d295345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293187, d294312, d295345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293187, d294312, d295345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75861 (p : Pattern) (ha : d293188 p = 1) (hb : d294313 p = 1) : d295346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293101 q = 1) (hb : d294222 q = 1) : d295260 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75837 q ha hb
    | true =>
      simp only [d293101, d294222, d295260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293102 q = 1) (hb : d294223 q = 1) : d295261 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293102, d294223, d295261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293107 q = 1) (hb : d294228 q = 1) : d295266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293107, d294228, d295266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293141 q = 1) (hb : d294262 q = 1) : d295300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293141, d294262, d295300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293141, d294262, d295300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293142 q = 1) (hb : d294263 q = 1) : d295301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293142, d294263, d295301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293142, d294263, d295301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293188 q = 1) (hb : d294313 q = 1) : d295346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293188, d294313, d295346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293188, d294313, d295346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75862 (p : Pattern) (ha : d293192 p = 1) (hb : d294317 p = 1) : d295350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293154 q = 1) (hb : d294279 q = 1) : d295312 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293154, d294279, d295312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75850 q ha hb
    | true =>
      simp only [d293154, d294279, d295312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293155 q = 1) (hb : d294280 q = 1) : d295313 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293155, d294280, d295313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293155, d294280, d295313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293097 q = 1) (hb : d294218 q = 1) : d295256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75836 q ha hb
    | true =>
      simp only [d293097, d294218, d295256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293098 q = 1) (hb : d294219 q = 1) : d295257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293098, d294219, d295257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293156 q = 1) (hb : d294281 q = 1) : d295314 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293156, d294281, d295314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293156, d294281, d295314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293157 q = 1) (hb : d294282 q = 1) : d295315 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293157, d294282, d295315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293157, d294282, d295315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293158 q = 1) (hb : d294283 q = 1) : d295316 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293158, d294283, d295316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293158, d294283, d295316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293192 q = 1) (hb : d294317 q = 1) : d295350 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293192, d294317, d295350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293192, d294317, d295350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75863 (p : Pattern) (ha : d293195 p = 1) (hb : d294320 p = 1) : d295353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293169 q = 1) (hb : d294294 q = 1) : d295327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293169, d294294, d295327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75855 q ha hb
    | true =>
      simp only [d293169, d294294, d295327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293170 q = 1) (hb : d294295 q = 1) : d295328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293170, d294295, d295328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293170, d294295, d295328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293171 q = 1) (hb : d294296 q = 1) : d295329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293171, d294296, d295329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293171, d294296, d295329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293172 q = 1) (hb : d294297 q = 1) : d295330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293172, d294297, d295330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293172, d294297, d295330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293173 q = 1) (hb : d294298 q = 1) : d295331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293173, d294298, d295331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293173, d294298, d295331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293195 q = 1) (hb : d294320 q = 1) : d295353 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293195, d294320, d295353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293195, d294320, d295353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75864 (p : Pattern) (ha : d293201 p = 1) (hb : d294326 p = 1) : d295359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293134 q = 1) (hb : d294255 q = 1) : d295293 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293134, d294255, d295293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75844 q ha hb
    | true =>
      simp only [d293134, d294255, d295293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75845 q ha hb
  have h2 (q : Pattern) (ha : d293135 q = 1) (hb : d294256 q = 1) : d295294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293135, d294256, d295294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293135, d294256, d295294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293136 q = 1) (hb : d294257 q = 1) : d295295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293136, d294257, d295295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293136, d294257, d295295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293137 q = 1) (hb : d294258 q = 1) : d295296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293137, d294258, d295296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293137, d294258, d295296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293144 q = 1) (hb : d294265 q = 1) : d295303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293144, d294265, d295303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75846 q ha hb
    | true =>
      simp only [d293144, d294265, d295303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75847 q ha hb
  have h6 (q : Pattern) (ha : d293145 q = 1) (hb : d294266 q = 1) : d295304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293145, d294266, d295304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293145, d294266, d295304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293146 q = 1) (hb : d294267 q = 1) : d295305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293146, d294267, d295305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293146, d294267, d295305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293160 q = 1) (hb : d294285 q = 1) : d295318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293160, d294285, d295318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75851 q ha hb
    | true =>
      simp only [d293160, d294285, d295318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75838 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d293111 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d293161 q = 1) (hb : d294286 q = 1) : d295319 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293161, d294286, d295319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293161, d294286, d295319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d293175 q = 1) (hb : d294300 q = 1) : d295333 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293175, d294300, d295333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75856 q ha hb
    | true =>
      simp only [d293175, d294300, d295333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d293176 q = 1) (hb : d294301 q = 1) : d295334 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293176, d294301, d295334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293176, d294301, d295334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d293177 q = 1) (hb : d294302 q = 1) : d295335 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293177, d294302, d295335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293177, d294302, d295335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293178 q = 1) (hb : d294303 q = 1) : d295336 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293178, d294303, d295336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293178, d294303, d295336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d293179 q = 1) (hb : d294304 q = 1) : d295337 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293179, d294304, d295337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293179, d294304, d295337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293183 q = 1) (hb : d294308 q = 1) : d295341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293183, d294308, d295341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75858 q ha hb
    | true =>
      simp only [d293183, d294308, d295341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75859 q ha hb
  have h17 (q : Pattern) (ha : d293184 q = 1) (hb : d294309 q = 1) : d295342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293184, d294309, d295342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293184, d294309, d295342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d293185 q = 1) (hb : d294310 q = 1) : d295343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293185, d294310, d295343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d293185, d294310, d295343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d293186 q = 1) (hb : d294311 q = 1) : d295344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293186, d294311, d295344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293186, d294311, d295344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d293189 q = 1) (hb : d294314 q = 1) : d295347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293189, d294314, d295347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75860 q ha hb
    | true =>
      simp only [d293189, d294314, d295347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75861 q ha hb
  have h21 (q : Pattern) (ha : d293190 q = 1) (hb : d294315 q = 1) : d295348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293190, d294315, d295348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293190, d294315, d295348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d293191 q = 1) (hb : d294316 q = 1) : d295349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293191, d294316, d295349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d293191, d294316, d295349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d293193 q = 1) (hb : d294318 q = 1) : d295351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293193, d294318, d295351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75862 q ha hb
    | true =>
      simp only [d293193, d294318, d295351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75841 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d293121 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d293194 q = 1) (hb : d294319 q = 1) : d295352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293194, d294319, d295352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d293194, d294319, d295352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d293196 q = 1) (hb : d294321 q = 1) : d295354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293196, d294321, d295354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75863 q ha hb
    | true =>
      simp only [d293196, d294321, d295354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d293197 q = 1) (hb : d294322 q = 1) : d295355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293197, d294322, d295355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d293197, d294322, d295355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d293198 q = 1) (hb : d294323 q = 1) : d295356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293198, d294323, d295356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d293198, d294323, d295356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d293199 q = 1) (hb : d294324 q = 1) : d295357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293199, d294324, d295357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d293199, d294324, d295357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d293200 q = 1) (hb : d294325 q = 1) : d295358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293200, d294325, d295358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d293200, d294325, d295358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d293201 q = 1) (hb : d294326 q = 1) : d295359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293201, d294326, d295359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d293201, d294326, d295359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro75865 (p : Pattern) (ha : d293208 p = 1) (hb : d294333 p = 1) : d295366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293111 q = 1) (hb : d294232 q = 1) : d295270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75838 q ha hb
    | true =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75839 q ha hb
  have h2 (q : Pattern) (ha : d293112 q = 1) (hb : d294233 q = 1) : d295271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293112, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293112, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293113 q = 1) (hb : d294234 q = 1) : d295272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293113, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293113, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293114 q = 1) (hb : d294235 q = 1) : d295273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293114, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293114, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293115 q = 1) (hb : d294236 q = 1) : d295274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293115, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293115, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293203 q = 1) (hb : d294328 q = 1) : d295361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293203, d294328, d295361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75839 q ha hb
    | true =>
      simp only [d293203, d294328, d295361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293204 q = 1) (hb : d294329 q = 1) : d295362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293204, d294329, d295362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293204, d294329, d295362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293205 q = 1) (hb : d294330 q = 1) : d295363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293205, d294330, d295363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293205, d294330, d295363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293206 q = 1) (hb : d294331 q = 1) : d295364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293206, d294331, d295364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293206, d294331, d295364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293207 q = 1) (hb : d294332 q = 1) : d295365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293207, d294332, d295365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293207, d294332, d295365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293208 q = 1) (hb : d294333 q = 1) : d295366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293208, d294333, d295366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293208, d294333, d295366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75866 (p : Pattern) (ha : d293214 p = 1) (hb : d294339 p = 1) : d295372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293203 q = 1) (hb : d294328 q = 1) : d295361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293203, d294328, d295361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75839 q ha hb
    | true =>
      simp only [d293203, d294328, d295361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293204 q = 1) (hb : d294329 q = 1) : d295362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293204, d294329, d295362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293204, d294329, d295362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293205 q = 1) (hb : d294330 q = 1) : d295363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293205, d294330, d295363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293205, d294330, d295363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293206 q = 1) (hb : d294331 q = 1) : d295364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293206, d294331, d295364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293206, d294331, d295364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293207 q = 1) (hb : d294332 q = 1) : d295365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293207, d294332, d295365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293207, d294332, d295365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293209 q = 1) (hb : d294334 q = 1) : d295367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293209, d294334, d295367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75842 q ha hb
    | true =>
      simp only [d293209, d294334, d295367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293210 q = 1) (hb : d294335 q = 1) : d295368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293210, d294335, d295368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293210, d294335, d295368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293211 q = 1) (hb : d294336 q = 1) : d295369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293211, d294336, d295369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293211, d294336, d295369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293212 q = 1) (hb : d294337 q = 1) : d295370 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293212, d294337, d295370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293212, d294337, d295370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293213 q = 1) (hb : d294338 q = 1) : d295371 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293213, d294338, d295371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293213, d294338, d295371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293214 q = 1) (hb : d294339 q = 1) : d295372 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293214, d294339, d295372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293214, d294339, d295372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75867 (p : Pattern) (ha : d293221 p = 1) (hb : d294346 p = 1) : d295379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293193 q = 1) (hb : d294318 q = 1) : d295351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293193, d294318, d295351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75862 q ha hb
    | true =>
      simp only [d293193, d294318, d295351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75841 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293194 q = 1) (hb : d294319 q = 1) : d295352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293194, d294319, d295352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293194, d294319, d295352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d293196 q = 1) (hb : d294321 q = 1) : d295354 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293196, d294321, d295354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75863 q ha hb
    | true =>
      simp only [d293196, d294321, d295354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293197 q = 1) (hb : d294322 q = 1) : d295355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293197, d294322, d295355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293197, d294322, d295355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293198 q = 1) (hb : d294323 q = 1) : d295356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293198, d294323, d295356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293198, d294323, d295356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293219 q = 1) (hb : d294344 q = 1) : d295377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293219, d294344, d295377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293219, d294344, d295377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293220 q = 1) (hb : d294345 q = 1) : d295378 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293220, d294345, d295378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293220, d294345, d295378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293221 q = 1) (hb : d294346 q = 1) : d295379 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293221, d294346, d295379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293221, d294346, d295379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro75868 (p : Pattern) (ha : d293223 p = 1) (hb : d294348 p = 1) : d295381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293209 q = 1) (hb : d294334 q = 1) : d295367 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293209, d294334, d295367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75842 q ha hb
    | true =>
      simp only [d293209, d294334, d295367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293210 q = 1) (hb : d294335 q = 1) : d295368 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293210, d294335, d295368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293210, d294335, d295368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293211 q = 1) (hb : d294336 q = 1) : d295369 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293211, d294336, d295369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293211, d294336, d295369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293212 q = 1) (hb : d294337 q = 1) : d295370 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293212, d294337, d295370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293212, d294337, d295370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293213 q = 1) (hb : d294338 q = 1) : d295371 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293213, d294338, d295371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293213, d294338, d295371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293223 q = 1) (hb : d294348 q = 1) : d295381 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293223, d294348, d295381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293223, d294348, d295381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75869 (p : Pattern) (ha : d293234 p = 1) (hb : d294359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156383 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156382 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293229 q = 1) (hb : d294354 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
  have h4 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d293230 q = 1) (hb : d294355 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d293231 q = 1) (hb : d294356 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293232 q = 1) (hb : d294357 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h9 (q : Pattern) (ha : d293233 q = 1) (hb : d294358 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293233, d294358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293233, d294358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293234 q = 1) (hb : d294359 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293234, d294359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293234, d294359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75870 (p : Pattern) (ha : d293240 p = 1) (hb : d294365 p = 1) : d295388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d293229 q = 1) (hb : d294354 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
  have h3 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d293230 q = 1) (hb : d294355 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d293231 q = 1) (hb : d294356 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293232 q = 1) (hb : d294357 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d293233 q = 1) (hb : d294358 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293233, d294358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293233, d294358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293238 q = 1) (hb : d294363 q = 1) : d294363 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d293239 q = 1) (hb : d294364 q = 1) : d295387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293239, d294364, d295387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293239, d294364, d295387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293240 q = 1) (hb : d294365 q = 1) : d295388 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293240, d294365, d295388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293240, d294365, d295388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75871 (p : Pattern) (ha : d293245 p = 1) (hb : d294370 p = 1) : d295392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293229 q = 1) (hb : d294354 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
  have h2 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293230 q = 1) (hb : d294355 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293231 q = 1) (hb : d294356 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293232 q = 1) (hb : d294357 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293238 q = 1) (hb : d294363 q = 1) : d294363 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d293239 q = 1) (hb : d294364 q = 1) : d295387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293239, d294364, d295387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293239, d294364, d295387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293244 q = 1) (hb : d294369 q = 1) : d294369 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d293245 q = 1) (hb : d294370 q = 1) : d295392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293245, d294370, d295392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293245, d294370, d295392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75872 (p : Pattern) (ha : d293245 p = 1) (hb : d294380 p = 1) : d295392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293229 q = 1) (hb : d294354 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
  have h2 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293230 q = 1) (hb : d294355 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293231 q = 1) (hb : d294356 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293232 q = 1) (hb : d294357 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293235 q = 1) (hb : d294375 q = 1) : d294360 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293235, d294375, d294360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293235, d294375, d294360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
  have h8 (q : Pattern) (ha : d293078 q = 1) (hb : d294199 q = 1) : d294189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
    | true =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293236 q = 1) (hb : d294376 q = 1) : d294361 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293236, d294376, d294361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293236, d294376, d294361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293079 q = 1) (hb : d294200 q = 1) : d294190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d293237 q = 1) (hb : d294377 q = 1) : d294362 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293237, d294377, d294362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293237, d294377, d294362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d293238 q = 1) (hb : d294378 q = 1) : d294363 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293238, d294378, d294363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293238, d294378, d294363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d293239 q = 1) (hb : d294379 q = 1) : d295387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293239, d294379, d295387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293239, d294379, d295387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293244 q = 1) (hb : d294369 q = 1) : d294369 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d293245 q = 1) (hb : d294380 q = 1) : d295392 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293245, d294380, d295392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293245, d294380, d295392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75873 (p : Pattern) (ha : d293250 p = 1) (hb : d294385 p = 1) : d295397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293235 q = 1) (hb : d294375 q = 1) : d294360 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293235, d294375, d294360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293235, d294375, d294360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
  have h2 (q : Pattern) (ha : d293078 q = 1) (hb : d294199 q = 1) : d294189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
    | true =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293236 q = 1) (hb : d294376 q = 1) : d294361 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293236, d294376, d294361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293236, d294376, d294361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293079 q = 1) (hb : d294200 q = 1) : d294190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293237 q = 1) (hb : d294377 q = 1) : d294362 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293237, d294377, d294362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293237, d294377, d294362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293238 q = 1) (hb : d294378 q = 1) : d294363 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293238, d294378, d294363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293238, d294378, d294363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293244 q = 1) (hb : d294384 q = 1) : d294369 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293244, d294384, d294369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293244, d294384, d294369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293250 q = 1) (hb : d294385 q = 1) : d295397 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293250, d294385, d295397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293250, d294385, d295397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75874 (p : Pattern) (ha : d293256 p = 1) (hb : d294391 p = 1) : d295403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293241 q = 1) (hb : d294366 q = 1) : d295389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293241, d294366, d295389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75869 q ha hb
    | true =>
      simp only [d293241, d294366, d295389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75870 q ha hb
  have h2 (q : Pattern) (ha : d293242 q = 1) (hb : d294367 q = 1) : d295390 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293242, d294367, d295390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293242, d294367, d295390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293243 q = 1) (hb : d294368 q = 1) : d295391 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293243, d294368, d295391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293243, d294368, d295391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293246 q = 1) (hb : d294371 q = 1) : d295393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293246, d294371, d295393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75870 q ha hb
    | true =>
      simp only [d293246, d294371, d295393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75871 q ha hb
  have h5 (q : Pattern) (ha : d293247 q = 1) (hb : d294372 q = 1) : d295394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293247, d294372, d295394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293247, d294372, d295394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293248 q = 1) (hb : d294373 q = 1) : d295395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293248, d294373, d295395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293248, d294373, d295395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293249 q = 1) (hb : d294374 q = 1) : d295396 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293249, d294374, d295396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293249, d294374, d295396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293246 q = 1) (hb : d294381 q = 1) : d295393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293246, d294381, d295393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75870 q ha hb
    | true =>
      simp only [d293246, d294381, d295393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75872 q ha hb
  have h9 (q : Pattern) (ha : d293247 q = 1) (hb : d294382 q = 1) : d295394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293247, d294382, d295394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293247, d294382, d295394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293248 q = 1) (hb : d294383 q = 1) : d295395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293248, d294383, d295395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293248, d294383, d295395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293251 q = 1) (hb : d294386 q = 1) : d295398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293251, d294386, d295398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75872 q ha hb
    | true =>
      simp only [d293251, d294386, d295398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75873 q ha hb
  have h12 (q : Pattern) (ha : d293252 q = 1) (hb : d294387 q = 1) : d295399 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293252, d294387, d295399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293252, d294387, d295399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293253 q = 1) (hb : d294388 q = 1) : d295400 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293253, d294388, d295400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293253, d294388, d295400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293254 q = 1) (hb : d294389 q = 1) : d295401 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293254, d294389, d295401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293254, d294389, d295401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d293255 q = 1) (hb : d294390 q = 1) : d295402 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293255, d294390, d295402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293255, d294390, d295402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293256 q = 1) (hb : d294391 q = 1) : d295403 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293256, d294391, d295403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d293256, d294391, d295403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro75875 (p : Pattern) (ha : d293261 p = 1) (hb : d294396 p = 1) : d295408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293246 q = 1) (hb : d294381 q = 1) : d295393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293246, d294381, d295393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75870 q ha hb
    | true =>
      simp only [d293246, d294381, d295393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75872 q ha hb
  have h2 (q : Pattern) (ha : d293247 q = 1) (hb : d294382 q = 1) : d295394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293247, d294382, d295394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293247, d294382, d295394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293248 q = 1) (hb : d294383 q = 1) : d295395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293248, d294383, d295395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293248, d294383, d295395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293251 q = 1) (hb : d294386 q = 1) : d295398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293251, d294386, d295398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75872 q ha hb
    | true =>
      simp only [d293251, d294386, d295398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75873 q ha hb
  have h5 (q : Pattern) (ha : d293252 q = 1) (hb : d294387 q = 1) : d295399 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293252, d294387, d295399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293252, d294387, d295399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293253 q = 1) (hb : d294388 q = 1) : d295400 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293253, d294388, d295400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293253, d294388, d295400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293254 q = 1) (hb : d294389 q = 1) : d295401 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293254, d294389, d295401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293254, d294389, d295401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293259 q = 1) (hb : d294394 q = 1) : d295406 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293259, d294394, d295406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293259, d294394, d295406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293260 q = 1) (hb : d294395 q = 1) : d295407 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293260, d294395, d295407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293260, d294395, d295407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293261 q = 1) (hb : d294396 q = 1) : d295408 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293261, d294396, d295408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293261, d294396, d295408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro75876 (p : Pattern) (ha : d293267 p = 1) (hb : d294402 p = 1) : d295414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293257 q = 1) (hb : d294392 q = 1) : d295404 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293257, d294392, d295404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75874 q ha hb
    | true =>
      simp only [d293257, d294392, d295404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293258 q = 1) (hb : d294393 q = 1) : d295405 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293258, d294393, d295405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293258, d294393, d295405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293262 q = 1) (hb : d294397 q = 1) : d295409 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293262, d294397, d295409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75875 q ha hb
    | true =>
      simp only [d293262, d294397, d295409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293263 q = 1) (hb : d294398 q = 1) : d295410 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293263, d294398, d295410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293263, d294398, d295410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293264 q = 1) (hb : d294399 q = 1) : d295411 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293264, d294399, d295411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293264, d294399, d295411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293265 q = 1) (hb : d294400 q = 1) : d295412 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293265, d294400, d295412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293265, d294400, d295412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293266 q = 1) (hb : d294401 q = 1) : d295413 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293266, d294401, d295413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293266, d294401, d295413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293267 q = 1) (hb : d294402 q = 1) : d295414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293267, d294402, d295414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293267, d294402, d295414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75877 (p : Pattern) (ha : d293269 p = 1) (hb : d294404 p = 1) : d295416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293251 q = 1) (hb : d294386 q = 1) : d295398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293251, d294386, d295398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75872 q ha hb
    | true =>
      simp only [d293251, d294386, d295398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75873 q ha hb
  have h2 (q : Pattern) (ha : d293252 q = 1) (hb : d294387 q = 1) : d295399 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293252, d294387, d295399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293252, d294387, d295399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293253 q = 1) (hb : d294388 q = 1) : d295400 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293253, d294388, d295400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293253, d294388, d295400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293259 q = 1) (hb : d294394 q = 1) : d295406 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293259, d294394, d295406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293259, d294394, d295406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293268 q = 1) (hb : d294403 q = 1) : d295415 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293268, d294403, d295415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293268, d294403, d295415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293269 q = 1) (hb : d294404 q = 1) : d295416 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293269, d294404, d295416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293269, d294404, d295416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75878 (p : Pattern) (ha : d293275 p = 1) (hb : d294410 p = 1) : d295422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293262 q = 1) (hb : d294397 q = 1) : d295409 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293262, d294397, d295409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75875 q ha hb
    | true =>
      simp only [d293262, d294397, d295409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293263 q = 1) (hb : d294398 q = 1) : d295410 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293263, d294398, d295410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293263, d294398, d295410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293270 q = 1) (hb : d294405 q = 1) : d295417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293270, d294405, d295417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75877 q ha hb
    | true =>
      simp only [d293270, d294405, d295417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293271 q = 1) (hb : d294406 q = 1) : d295418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293271, d294406, d295418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293271, d294406, d295418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293272 q = 1) (hb : d294407 q = 1) : d295419 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293272, d294407, d295419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293272, d294407, d295419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293273 q = 1) (hb : d294408 q = 1) : d295420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293273, d294408, d295420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293273, d294408, d295420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293274 q = 1) (hb : d294409 q = 1) : d295421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293274, d294409, d295421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293274, d294409, d295421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d293275 q = 1) (hb : d294410 q = 1) : d295422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293275, d294410, d295422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293275, d294410, d295422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75879 (p : Pattern) (ha : d156412 p = 1) (hb : d207336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156407 q = 1) (hb : d207331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156407, d207331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156407, d207331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75852 q ha hb
  have h2 (q : Pattern) (ha : d156219 q = 1) (hb : d207151 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156219, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75852 q ha hb
    | true =>
      simp only [d156219, d207151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156408 q = 1) (hb : d207332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156408, d207332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156408, d207332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156220 q = 1) (hb : d207152 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156220, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156220, d207152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156409 q = 1) (hb : d207333 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156409, d207333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156409, d207333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156410 q = 1) (hb : d207334 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156410, d207334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156410, d207334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156411 q = 1) (hb : d207335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156411, d207335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156411, d207335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156412 q = 1) (hb : d207336 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156412, d207336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156412, d207336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro75880 (p : Pattern) (ha : d293283 p = 1) (hb : d294413 p = 1) : d295425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293229 q = 1) (hb : d294354 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293229, d294354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
  have h2 (q : Pattern) (ha : d293071 q = 1) (hb : d294180 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75831 q ha hb
    | true =>
      simp only [d293071, d294180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293230 q = 1) (hb : d294355 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293230, d294355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293072 q = 1) (hb : d294181 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293072, d294181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293231 q = 1) (hb : d294356 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293231, d294356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293232 q = 1) (hb : d294357 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293232, d294357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d293235 q = 1) (hb : d294375 q = 1) : d294360 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293235, d294375, d294360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293235, d294375, d294360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
  have h8 (q : Pattern) (ha : d293078 q = 1) (hb : d294199 q = 1) : d294189 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75833 q ha hb
    | true =>
      simp only [d293078, d294199, d294189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d293236 q = 1) (hb : d294376 q = 1) : d294361 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293236, d294376, d294361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293236, d294376, d294361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293079 q = 1) (hb : d294200 q = 1) : d294190 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293079, d294200, d294190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d293237 q = 1) (hb : d294377 q = 1) : d294362 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d293237, d294377, d294362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293237, d294377, d294362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d293238 q = 1) (hb : d294378 q = 1) : d294363 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d293238, d294378, d294363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293238, d294378, d294363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d293239 q = 1) (hb : d294379 q = 1) : d295387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d293239, d294379, d295387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293239, d294379, d295387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d156411 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d293283 q = 1) (hb : d294413 q = 1) : d295425 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d293283, d294413, d295425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293283, d294413, d295425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro75881 (p : Pattern) (ha : d293289 p = 1) (hb : d294419 p = 1) : d295431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293246 q = 1) (hb : d294381 q = 1) : d295393 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293246, d294381, d295393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75870 q ha hb
    | true =>
      simp only [d293246, d294381, d295393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75872 q ha hb
  have h2 (q : Pattern) (ha : d293247 q = 1) (hb : d294382 q = 1) : d295394 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293247, d294382, d295394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293247, d294382, d295394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293248 q = 1) (hb : d294383 q = 1) : d295395 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293248, d294383, d295395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293248, d294383, d295395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293251 q = 1) (hb : d294386 q = 1) : d295398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293251, d294386, d295398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75872 q ha hb
    | true =>
      simp only [d293251, d294386, d295398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75873 q ha hb
  have h5 (q : Pattern) (ha : d293252 q = 1) (hb : d294387 q = 1) : d295399 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293252, d294387, d295399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293252, d294387, d295399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293253 q = 1) (hb : d294388 q = 1) : d295400 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293253, d294388, d295400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293253, d294388, d295400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293254 q = 1) (hb : d294389 q = 1) : d295401 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293254, d294389, d295401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293254, d294389, d295401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293284 q = 1) (hb : d294414 q = 1) : d295426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d293284, d294414, d295426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75880 q ha hb
    | true =>
      simp only [d293284, d294414, d295426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75879 q ha hb
  have h9 (q : Pattern) (ha : d293285 q = 1) (hb : d294415 q = 1) : d295427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d293285, d294415, d295427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293285, d294415, d295427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293286 q = 1) (hb : d294416 q = 1) : d295428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d293286, d294416, d295428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293286, d294416, d295428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293287 q = 1) (hb : d294417 q = 1) : d295429 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d293287, d294417, d295429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293287, d294417, d295429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d293288 q = 1) (hb : d294418 q = 1) : d295430 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d293288, d294418, d295430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293288, d294418, d295430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293289 q = 1) (hb : d294419 q = 1) : d295431 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d293289, d294419, d295431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d293289, d294419, d295431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro75882 (p : Pattern) (ha : d293295 p = 1) (hb : d294425 p = 1) : d295437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293290 q = 1) (hb : d294420 q = 1) : d295432 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293290, d294420, d295432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75881 q ha hb
    | true =>
      simp only [d293290, d294420, d295432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293291 q = 1) (hb : d294421 q = 1) : d295433 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293291, d294421, d295433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293291, d294421, d295433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293292 q = 1) (hb : d294422 q = 1) : d295434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293292, d294422, d295434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293292, d294422, d295434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293293 q = 1) (hb : d294423 q = 1) : d295435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293293, d294423, d295435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293293, d294423, d295435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293294 q = 1) (hb : d294424 q = 1) : d295436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293294, d294424, d295436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293294, d294424, d295436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293295 q = 1) (hb : d294425 q = 1) : d295437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293295, d294425, d295437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293295, d294425, d295437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75883 (p : Pattern) (ha : d293301 p = 1) (hb : d294431 p = 1) : d295443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293276 q = 1) (hb : d294411 q = 1) : d295423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293276, d294411, d295423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75876 q ha hb
    | true =>
      simp only [d293276, d294411, d295423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75878 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293281 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293282 q = 1) (hb : d294412 q = 1) : d295424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293282, d294412, d295424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293282, d294412, d295424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d293296 q = 1) (hb : d294426 q = 1) : d295438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293296, d294426, d295438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75882 q ha hb
    | true =>
      simp only [d293296, d294426, d295438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293297 q = 1) (hb : d294427 q = 1) : d295439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293297, d294427, d295439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293297, d294427, d295439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293298 q = 1) (hb : d294428 q = 1) : d295440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293298, d294428, d295440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293298, d294428, d295440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293299 q = 1) (hb : d294429 q = 1) : d295441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293299, d294429, d295441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293299, d294429, d295441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293300 q = 1) (hb : d294430 q = 1) : d295442 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293300, d294430, d295442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293300, d294430, d295442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293301 q = 1) (hb : d294431 q = 1) : d295443 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293301, d294431, d295443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293301, d294431, d295443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro75884 (p : Pattern) (ha : d293280 p = 1) (hb : d294436 p = 1) : d295448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293270 q = 1) (hb : d294405 q = 1) : d295417 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d293270, d294405, d295417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75877 q ha hb
    | true =>
      simp only [d293270, d294405, d295417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293271 q = 1) (hb : d294406 q = 1) : d295418 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d293271, d294406, d295418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293271, d294406, d295418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293277 q = 1) (hb : d294433 q = 1) : d295445 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d293277, d294433, d295445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293277, d294433, d295445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293278 q = 1) (hb : d294434 q = 1) : d295446 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d293278, d294434, d295446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293278, d294434, d295446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293279 q = 1) (hb : d294435 q = 1) : d295447 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d293279, d294435, d295447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293279, d294435, d295447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293280 q = 1) (hb : d294436 q = 1) : d295448 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d293280, d294436, d295448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293280, d294436, d295448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75885 (p : Pattern) (ha : d293308 p = 1) (hb : d294442 p = 1) : d295454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293303 q = 1) (hb : d294437 q = 1) : d295449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293303, d294437, d295449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75884 q ha hb
    | true =>
      simp only [d293303, d294437, d295449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293304 q = 1) (hb : d294438 q = 1) : d295450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293304, d294438, d295450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293304, d294438, d295450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293305 q = 1) (hb : d294439 q = 1) : d295451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293305, d294439, d295451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293305, d294439, d295451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293306 q = 1) (hb : d294440 q = 1) : d295452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293306, d294440, d295452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293306, d294440, d295452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293307 q = 1) (hb : d294441 q = 1) : d295453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293307, d294441, d295453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293307, d294441, d295453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293308 q = 1) (hb : d294442 q = 1) : d295454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293308, d294442, d295454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293308, d294442, d295454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75886 (p : Pattern) (ha : d293314 p = 1) (hb : d294448 p = 1) : d295460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293117 q = 1) (hb : d294238 q = 1) : d295276 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293117, d294238, d295276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293117, d294238, d295276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75840 q ha hb
  have h2 (q : Pattern) (ha : d293118 q = 1) (hb : d294239 q = 1) : d295277 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293118, d294239, d295277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293118, d294239, d295277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293127 q = 1) (hb : d294248 q = 1) : d295286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293127, d294248, d295286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75840 q ha hb
    | true =>
      simp only [d293127, d294248, d295286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75843 q ha hb
  have h4 (q : Pattern) (ha : d293128 q = 1) (hb : d294249 q = 1) : d295287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293128, d294249, d295287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293128, d294249, d295287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293129 q = 1) (hb : d294250 q = 1) : d295288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293129, d294250, d295288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293129, d294250, d295288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293202 q = 1) (hb : d294327 q = 1) : d295360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293202, d294327, d295360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75857 q ha hb
    | true =>
      simp only [d293202, d294327, d295360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75864 q ha hb
  have h7 (q : Pattern) (ha : d293215 q = 1) (hb : d294340 q = 1) : d295373 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293215, d294340, d295373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75865 q ha hb
    | true =>
      simp only [d293215, d294340, d295373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75866 q ha hb
  have h8 (q : Pattern) (ha : d293216 q = 1) (hb : d294341 q = 1) : d295374 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293216, d294341, d295374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293216, d294341, d295374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293217 q = 1) (hb : d294342 q = 1) : d295375 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293217, d294342, d295375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293217, d294342, d295375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d293218 q = 1) (hb : d294343 q = 1) : d295376 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d293218, d294343, d295376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293218, d294343, d295376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293222 q = 1) (hb : d294347 q = 1) : d295380 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293222, d294347, d295380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293222, d294347, d295380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75867 q ha hb
  have h12 (q : Pattern) (ha : d293224 q = 1) (hb : d294349 q = 1) : d295382 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293224, d294349, d295382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293224, d294349, d295382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75868 q ha hb
  have h13 (q : Pattern) (ha : d293225 q = 1) (hb : d294350 q = 1) : d295383 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293225, d294350, d295383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293225, d294350, d295383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293226 q = 1) (hb : d294351 q = 1) : d295384 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293226, d294351, d295384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293226, d294351, d295384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d293227 q = 1) (hb : d294352 q = 1) : d295385 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d293227, d294352, d295385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d293227, d294352, d295385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d293228 q = 1) (hb : d294353 q = 1) : d295386 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d293228, d294353, d295386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293228, d294353, d295386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d293302 q = 1) (hb : d294432 q = 1) : d295444 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293302, d294432, d295444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293302, d294432, d295444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75883 q ha hb
  have h18 (q : Pattern) (ha : d293309 q = 1) (hb : d294443 q = 1) : d295455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293309, d294443, d295455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293309, d294443, d295455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75885 q ha hb
  have h19 (q : Pattern) (ha : d293310 q = 1) (hb : d294444 q = 1) : d295456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293310, d294444, d295456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d293310, d294444, d295456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d293311 q = 1) (hb : d294445 q = 1) : d295457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293311, d294445, d295457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d293311, d294445, d295457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d293312 q = 1) (hb : d294446 q = 1) : d295458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d293312, d294446, d295458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d293312, d294446, d295458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d293313 q = 1) (hb : d294447 q = 1) : d295459 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d293313, d294447, d295459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d293313, d294447, d295459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d293314 q = 1) (hb : d294448 q = 1) : d295460 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d293314, d294448, d295460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d293314, d294448, d295460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro75887 (p : Pattern) (ha : d293320 p = 1) (hb : d294454 p = 1) : d295466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293315 q = 1) (hb : d294449 q = 1) : d295461 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d293315, d294449, d295461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293315, d294449, d295461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75886 q ha hb
  have h2 (q : Pattern) (ha : d293316 q = 1) (hb : d294450 q = 1) : d295462 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d293316, d294450, d295462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293316, d294450, d295462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293317 q = 1) (hb : d294451 q = 1) : d295463 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d293317, d294451, d295463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293317, d294451, d295463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293318 q = 1) (hb : d294452 q = 1) : d295464 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d293318, d294452, d295464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293318, d294452, d295464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293319 q = 1) (hb : d294453 q = 1) : d295465 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d293319, d294453, d295465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293319, d294453, d295465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293320 q = 1) (hb : d294454 q = 1) : d295466 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d293320, d294454, d295466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293320, d294454, d295466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75888 (p : Pattern) (ha : d293326 p = 1) (hb : d294460 p = 1) : d295472 p = 1 := by
  have h0 (q : Pattern) (ha : d292221 q = 1) (hb : d293451 q = 1) : d294583 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d292221, d293451, d294583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75635 q ha hb
    | true =>
      simp only [d292221, d293451, d294583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75663 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292464 q = 1) (hb : d293627 q = 1) : d294804 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d292464, d293627, d294804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292464, d293627, d294804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75712 q ha hb
  have h3 (q : Pattern) (ha : d292465 q = 1) (hb : d293628 q = 1) : d294805 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d292465, d293628, d294805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d292465, d293628, d294805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292754 q = 1) (hb : d293883 q = 1) : d295028 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d292754, d293883, d295028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292754, d293883, d295028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75769 q ha hb
  have h5 (q : Pattern) (ha : d292755 q = 1) (hb : d293884 q = 1) : d295029 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d292755, d293884, d295029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292755, d293884, d295029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292756 q = 1) (hb : d293885 q = 1) : d295030 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d292756, d293885, d295030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292756, d293885, d295030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293065 q = 1) (hb : d294175 q = 1) : d295238 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d293065, d294175, d295238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293065, d294175, d295238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75830 q ha hb
  have h8 (q : Pattern) (ha : d293066 q = 1) (hb : d294176 q = 1) : d295239 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d293066, d294176, d295239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293066, d294176, d295239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293067 q = 1) (hb : d294177 q = 1) : d295240 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d293067, d294177, d295240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293067, d294177, d295240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293068 q = 1) (hb : d294178 q = 1) : d295241 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d293068, d294178, d295241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293068, d294178, d295241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293321 q = 1) (hb : d294455 q = 1) : d295467 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d293321, d294455, d295467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293321, d294455, d295467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75887 q ha hb
  have h12 (q : Pattern) (ha : d293322 q = 1) (hb : d294456 q = 1) : d295468 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d293322, d294456, d295468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293322, d294456, d295468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293323 q = 1) (hb : d294457 q = 1) : d295469 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d293323, d294457, d295469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293323, d294457, d295469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293324 q = 1) (hb : d294458 q = 1) : d295470 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d293324, d294458, d295470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293324, d294458, d295470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d293325 q = 1) (hb : d294459 q = 1) : d295471 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d293325, d294459, d295471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293325, d294459, d295471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293326 q = 1) (hb : d294460 q = 1) : d295472 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d293326, d294460, d295472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d293326, d294460, d295472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro75889 (p : Pattern) (ha : d293332 p = 1) (hb : d294466 p = 1) : d295478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293327 q = 1) (hb : d294461 q = 1) : d295473 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d293327, d294461, d295473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75888 q ha hb
    | true =>
      simp only [d293327, d294461, d295473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293328 q = 1) (hb : d294462 q = 1) : d295474 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d293328, d294462, d295474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293328, d294462, d295474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293329 q = 1) (hb : d294463 q = 1) : d295475 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d293329, d294463, d295475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293329, d294463, d295475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293330 q = 1) (hb : d294464 q = 1) : d295476 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d293330, d294464, d295476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293330, d294464, d295476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293331 q = 1) (hb : d294465 q = 1) : d295477 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d293331, d294465, d295477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293331, d294465, d295477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293332 q = 1) (hb : d294466 q = 1) : d295478 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d293332, d294466, d295478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293332, d294466, d295478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75890 (p : Pattern) (ha : d293338 p = 1) (hb : d294472 p = 1) : d295484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293333 q = 1) (hb : d294467 q = 1) : d295479 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d293333, d294467, d295479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75889 q ha hb
    | true =>
      simp only [d293333, d294467, d295479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293334 q = 1) (hb : d294468 q = 1) : d295480 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d293334, d294468, d295480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293334, d294468, d295480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293335 q = 1) (hb : d294469 q = 1) : d295481 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d293335, d294469, d295481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293335, d294469, d295481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293336 q = 1) (hb : d294470 q = 1) : d295482 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d293336, d294470, d295482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293336, d294470, d295482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293337 q = 1) (hb : d294471 q = 1) : d295483 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d293337, d294471, d295483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293337, d294471, d295483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293338 q = 1) (hb : d294472 q = 1) : d295484 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d293338, d294472, d295484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293338, d294472, d295484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75891 (p : Pattern) (ha : d293344 p = 1) (hb : d294478 p = 1) : d295490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293339 q = 1) (hb : d294473 q = 1) : d295485 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d293339, d294473, d295485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75890 q ha hb
    | true =>
      simp only [d293339, d294473, d295485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293340 q = 1) (hb : d294474 q = 1) : d295486 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d293340, d294474, d295486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293340, d294474, d295486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293341 q = 1) (hb : d294475 q = 1) : d295487 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d293341, d294475, d295487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293341, d294475, d295487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293342 q = 1) (hb : d294476 q = 1) : d295488 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d293342, d294476, d295488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293342, d294476, d295488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293343 q = 1) (hb : d294477 q = 1) : d295489 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d293343, d294477, d295489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293343, d294477, d295489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293344 q = 1) (hb : d294478 q = 1) : d295490 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d293344, d294478, d295490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293344, d294478, d295490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75892 (p : Pattern) (ha : d293350 p = 1) (hb : d294484 p = 1) : d295496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293345 q = 1) (hb : d294479 q = 1) : d295491 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d293345, d294479, d295491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75891 q ha hb
    | true =>
      simp only [d293345, d294479, d295491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293346 q = 1) (hb : d294480 q = 1) : d295492 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d293346, d294480, d295492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293346, d294480, d295492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293347 q = 1) (hb : d294481 q = 1) : d295493 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d293347, d294481, d295493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293347, d294481, d295493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293348 q = 1) (hb : d294482 q = 1) : d295494 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d293348, d294482, d295494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293348, d294482, d295494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293349 q = 1) (hb : d294483 q = 1) : d295495 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d293349, d294483, d295495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293349, d294483, d295495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293350 q = 1) (hb : d294484 q = 1) : d295496 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d293350, d294484, d295496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293350, d294484, d295496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75893 (p : Pattern) (ha : d293356 p = 1) (hb : d294490 p = 1) : d295502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293351 q = 1) (hb : d294485 q = 1) : d295497 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d293351, d294485, d295497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75892 q ha hb
    | true =>
      simp only [d293351, d294485, d295497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293352 q = 1) (hb : d294486 q = 1) : d295498 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d293352, d294486, d295498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293352, d294486, d295498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293353 q = 1) (hb : d294487 q = 1) : d295499 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d293353, d294487, d295499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293353, d294487, d295499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293354 q = 1) (hb : d294488 q = 1) : d295500 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d293354, d294488, d295500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293354, d294488, d295500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293355 q = 1) (hb : d294489 q = 1) : d295501 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d293355, d294489, d295501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293355, d294489, d295501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293356 q = 1) (hb : d294490 q = 1) : d295502 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d293356, d294490, d295502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293356, d294490, d295502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75894 (p : Pattern) (ha : d293362 p = 1) (hb : d294496 p = 1) : d295508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293357 q = 1) (hb : d294491 q = 1) : d295503 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d293357, d294491, d295503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75893 q ha hb
    | true =>
      simp only [d293357, d294491, d295503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293358 q = 1) (hb : d294492 q = 1) : d295504 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d293358, d294492, d295504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293358, d294492, d295504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293359 q = 1) (hb : d294493 q = 1) : d295505 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d293359, d294493, d295505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293359, d294493, d295505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293360 q = 1) (hb : d294494 q = 1) : d295506 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d293360, d294494, d295506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293360, d294494, d295506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293361 q = 1) (hb : d294495 q = 1) : d295507 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d293361, d294495, d295507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293361, d294495, d295507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293362 q = 1) (hb : d294496 q = 1) : d295508 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d293362, d294496, d295508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293362, d294496, d295508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75895 (p : Pattern) (ha : d293368 p = 1) (hb : d294502 p = 1) : d295514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293363 q = 1) (hb : d294497 q = 1) : d295509 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d293363, d294497, d295509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75894 q ha hb
    | true =>
      simp only [d293363, d294497, d295509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293364 q = 1) (hb : d294498 q = 1) : d295510 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d293364, d294498, d295510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293364, d294498, d295510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293365 q = 1) (hb : d294499 q = 1) : d295511 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d293365, d294499, d295511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293365, d294499, d295511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293366 q = 1) (hb : d294500 q = 1) : d295512 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d293366, d294500, d295512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293366, d294500, d295512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293367 q = 1) (hb : d294501 q = 1) : d295513 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d293367, d294501, d295513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293367, d294501, d295513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293368 q = 1) (hb : d294502 q = 1) : d295514 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d293368, d294502, d295514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293368, d294502, d295514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75896 (p : Pattern) (ha : d202307 p = 1) (hb : d282071 p = 1) : d206194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30664 q = 1) (hb : d202307 q = 1) : d205920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75276 q ha hb
    | true =>
      simp only [d30664, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47892 q ha hb
  have h2 (q : Pattern) (ha : d30724 q = 1) (hb : d202307 q = 1) : d205978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30724, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30724, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30725 q = 1) (hb : d202307 q = 1) : d205979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30725, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30725, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30726 q = 1) (hb : d202307 q = 1) : d205980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30726, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30726, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30727 q = 1) (hb : d202307 q = 1) : d205981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30727, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30727, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282071 q = 1) : d206194 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282071, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282071, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro75897 (p : Pattern) (ha : d202307 p = 1) (hb : d282081 p = 1) : d206240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30700 q = 1) (hb : d202307 q = 1) : d205954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30700, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75281 q ha hb
    | true =>
      simp only [d30700, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47897 q ha hb
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d282077 q = 1) : d206236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282077, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282077, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282078 q = 1) : d206237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282078, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282078, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d282079 q = 1) : d206238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282079, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282079, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d282080 q = 1) : d206239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282080, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282080, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282081 q = 1) : d206240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282081, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282081, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75898 (p : Pattern) (ha : d202307 p = 1) (hb : d282087 p = 1) : d207465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30729 q = 1) (hb : d202307 q = 1) : d205983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30729, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75284 q ha hb
    | true =>
      simp only [d30729, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75285 q ha hb
  have h2 (q : Pattern) (ha : d30730 q = 1) (hb : d202307 q = 1) : d205984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30730, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30730, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282069 q = 1) : d207455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282069, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d282069, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d282070 q = 1) : d207456 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282070, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282070, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d282072 q = 1) : d206195 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282072, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282072, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75896 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282073 q = 1) : d207457 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282073, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282073, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d202307 q = 1) (hb : d282074 q = 1) : d207458 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282074, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282074, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d202307 q = 1) (hb : d282075 q = 1) : d207459 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282075, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282075, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d202307 q = 1) (hb : d282076 q = 1) : d207460 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282076, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282076, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202307 q = 1) (hb : d282082 q = 1) : d206241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282082, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282082, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75897 q ha hb
  have h11 (q : Pattern) (ha : d202307 q = 1) (hb : d282083 q = 1) : d207461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282083, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282083, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d202307 q = 1) (hb : d282084 q = 1) : d207462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282084, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282084, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d202307 q = 1) (hb : d282085 q = 1) : d207463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282085, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282085, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d202307 q = 1) (hb : d282086 q = 1) : d207464 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282086, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282086, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d202307 q = 1) (hb : d282087 q = 1) : d207465 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282087, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282087, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75899 (p : Pattern) (ha : d202307 p = 1) (hb : d282093 p = 1) : d207471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48588 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282088 q = 1) : d207466 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282088, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282088, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75898 q ha hb
  have h7 (q : Pattern) (ha : d202307 q = 1) (hb : d282089 q = 1) : d207467 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282089, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282089, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202307 q = 1) (hb : d282090 q = 1) : d207468 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282090, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282090, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202307 q = 1) (hb : d282091 q = 1) : d207469 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282091, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282091, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202307 q = 1) (hb : d282092 q = 1) : d207470 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282092, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282092, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202307 q = 1) (hb : d282093 q = 1) : d207471 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282093, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d282093, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro75900 (p : Pattern) (ha : d202307 p = 1) (hb : d282096 p = 1) : d207474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30940 q = 1) (hb : d202307 q = 1) : d206036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30940, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75314 q ha hb
    | true =>
      simp only [d30940, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75315 q ha hb
  have h2 (q : Pattern) (ha : d30941 q = 1) (hb : d202307 q = 1) : d206099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30941, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30941, d206099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30942 q = 1) (hb : d202307 q = 1) : d206100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30942, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30942, d206100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30943 q = 1) (hb : d202307 q = 1) : d206101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30943, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30943, d206101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30944 q = 1) (hb : d202307 q = 1) : d206102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30944, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30944, d206102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282096 q = 1) : d207474 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282096, d207474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282096, d207474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro75901 (p : Pattern) (ha : d202307 p = 1) (hb : d282107 p = 1) : d207484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d282102 q = 1) : d206074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d282102, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75349 q hb ha
    | true =>
      simp only [d282102, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75321 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d282103 q = 1) : d207480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282103, d207480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282103, d207480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282104 q = 1) : d207481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282104, d207481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282104, d207481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d282105 q = 1) : d207482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282105, d207482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282105, d207482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d282106 q = 1) : d207483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282106, d207483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282106, d207483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282107 q = 1) : d207484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282107, d207484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282107, d207484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75902 (p : Pattern) (ha : d202307 p = 1) (hb : d282113 p = 1) : d207490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30946 q = 1) (hb : d202307 q = 1) : d206104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30946, d206104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75313 q ha hb
    | true =>
      simp only [d30946, d206104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75316 q ha hb
  have h2 (q : Pattern) (ha : d30947 q = 1) (hb : d202307 q = 1) : d206105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30947, d206105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30947, d206105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282094 q = 1) : d207472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282094, d207472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d282094, d207472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d282095 q = 1) : d207473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282095, d207473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282095, d207473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d282097 q = 1) : d207475 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282097, d207475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282097, d207475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75900 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282098 q = 1) : d207476 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282098, d207476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282098, d207476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d202307 q = 1) (hb : d282099 q = 1) : d207477 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282099, d207477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282099, d207477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d202307 q = 1) (hb : d282100 q = 1) : d207478 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282100, d207478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282100, d207478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d202307 q = 1) (hb : d282101 q = 1) : d207479 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282101, d207479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282101, d207479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202307 q = 1) (hb : d282108 q = 1) : d207485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282108, d207485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282108, d207485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75901 q ha hb
  have h11 (q : Pattern) (ha : d202307 q = 1) (hb : d282109 q = 1) : d207486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282109, d207486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282109, d207486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d202307 q = 1) (hb : d282110 q = 1) : d207487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282110, d207487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282110, d207487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d202307 q = 1) (hb : d282111 q = 1) : d207488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282111, d207488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282111, d207488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d202307 q = 1) (hb : d282112 q = 1) : d207489 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282112, d207489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282112, d207489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d202307 q = 1) (hb : d282113 q = 1) : d207490 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282113, d207490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282113, d207490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75903 (p : Pattern) (ha : d202307 p = 1) (hb : d282119 p = 1) : d207496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d282114 q = 1) : d207491 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282114, d207491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282114, d207491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75902 q ha hb
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d282115 q = 1) : d207492 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282115, d207492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282115, d207492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282116 q = 1) : d207493 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282116, d207493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282116, d207493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d282117 q = 1) : d207494 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282117, d207494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282117, d207494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d282118 q = 1) : d207495 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282118, d207495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282118, d207495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282119 q = 1) : d207496 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282119, d207496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282119, d207496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75904 (p : Pattern) (ha : d202307 p = 1) (hb : d282123 p = 1) : d295517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31276 q = 1) (hb : d202307 q = 1) : d293469 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31276, d293469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75363 q ha hb
    | true =>
      simp only [d31276, d293469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75364 q ha hb
  have h2 (q : Pattern) (ha : d31277 q = 1) (hb : d202307 q = 1) : d293470 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d293470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31277, d293470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31278 q = 1) (hb : d202307 q = 1) : d293471 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d293471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31278, d293471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31279 q = 1) (hb : d202307 q = 1) : d293472 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d293472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31279, d293472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31280 q = 1) (hb : d202307 q = 1) : d293473 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d293473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31280, d293473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282123 q = 1) : d295517 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282123, d295517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282123, d295517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro75905 (p : Pattern) (ha : d202307 p = 1) (hb : d282134 p = 1) : d295528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d282129 q = 1) : d295523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d282129, d295523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75401 q hb ha
    | true =>
      simp only [d282129, d295523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75372 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d282130 q = 1) : d295524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282130, d295524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282130, d295524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282131 q = 1) : d295525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282131, d295525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282131, d295525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d282132 q = 1) : d295526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282132, d295526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282132, d295526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d282133 q = 1) : d295527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282133, d295527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282133, d295527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282134 q = 1) : d295528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282134, d295528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282134, d295528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75906 (p : Pattern) (ha : d202307 p = 1) (hb : d282140 p = 1) : d295534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31282 q = 1) (hb : d202307 q = 1) : d293475 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31282, d293475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75362 q ha hb
    | true =>
      simp only [d31282, d293475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75365 q ha hb
  have h2 (q : Pattern) (ha : d31283 q = 1) (hb : d202307 q = 1) : d293476 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31283, d293476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31283, d293476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282121 q = 1) : d295515 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282121, d295515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d282121, d295515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d282122 q = 1) : d295516 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282122, d295516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282122, d295516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d282124 q = 1) : d295518 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282124, d295518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282124, d295518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75904 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282125 q = 1) : d295519 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282125, d295519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282125, d295519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d202307 q = 1) (hb : d282126 q = 1) : d295520 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282126, d295520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282126, d295520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d202307 q = 1) (hb : d282127 q = 1) : d295521 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282127, d295521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282127, d295521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d202307 q = 1) (hb : d282128 q = 1) : d295522 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282128, d295522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282128, d295522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202307 q = 1) (hb : d282135 q = 1) : d295529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282135, d295529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282135, d295529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75905 q ha hb
  have h11 (q : Pattern) (ha : d202307 q = 1) (hb : d282136 q = 1) : d295530 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282136, d295530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282136, d295530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d202307 q = 1) (hb : d282137 q = 1) : d295531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282137, d295531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282137, d295531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d202307 q = 1) (hb : d282138 q = 1) : d295532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282138, d295532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282138, d295532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d202307 q = 1) (hb : d282139 q = 1) : d295533 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282139, d295533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282139, d295533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d202307 q = 1) (hb : d282140 q = 1) : d295534 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282140, d295534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282140, d295534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75907 (p : Pattern) (ha : d202307 p = 1) (hb : d282146 p = 1) : d295540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d282141 q = 1) : d295535 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282141, d295535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282141, d295535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75906 q ha hb
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d282142 q = 1) : d295536 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282142, d295536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282142, d295536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282143 q = 1) : d295537 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282143, d295537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282143, d295537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d282144 q = 1) : d295538 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282144, d295538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282144, d295538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d282145 q = 1) : d295539 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282145, d295539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282145, d295539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d282146 q = 1) : d295540 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282146, d295540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282146, d295540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75908 (p : Pattern) (ha : d202307 p = 1) (hb : d290378 p = 1) : d295545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31710 q = 1) (hb : d202307 q = 1) : d293667 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31710, d293667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75420 q ha hb
    | true =>
      simp only [d31710, d293667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75421 q ha hb
  have h2 (q : Pattern) (ha : d31711 q = 1) (hb : d202307 q = 1) : d293668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31711, d293668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31711, d293668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31712 q = 1) (hb : d202307 q = 1) : d293669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31712, d293669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31712, d293669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31713 q = 1) (hb : d202307 q = 1) : d293670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31713, d293670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31713, d293670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31714 q = 1) (hb : d202307 q = 1) : d293671 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31714, d293671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31714, d293671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290378 q = 1) : d295545 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290378, d295545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290378, d295545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro75909 (p : Pattern) (ha : d202307 p = 1) (hb : d290389 p = 1) : d295556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290384 q = 1) : d295551 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290384, d295551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75461 q hb ha
    | true =>
      simp only [d290384, d295551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75429 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290385 q = 1) : d295552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290385, d295552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290385, d295552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290386 q = 1) : d295553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290386, d295553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290386, d295553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290387 q = 1) : d295554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290387, d295554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290387, d295554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290388 q = 1) : d295555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290388, d295555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290388, d295555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290389 q = 1) : d295556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290389, d295556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290389, d295556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75910 (p : Pattern) (ha : d202307 p = 1) (hb : d290395 p = 1) : d295562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31716 q = 1) (hb : d202307 q = 1) : d293673 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31716, d293673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75419 q ha hb
    | true =>
      simp only [d31716, d293673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75422 q ha hb
  have h2 (q : Pattern) (ha : d31717 q = 1) (hb : d202307 q = 1) : d293674 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31717, d293674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31717, d293674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290376 q = 1) : d295543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290376, d295543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290376, d295543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290377 q = 1) : d295544 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290377, d295544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290377, d295544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290379 q = 1) : d295546 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290379, d295546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290379, d295546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75908 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290380 q = 1) : d295547 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290380, d295547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290380, d295547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d202307 q = 1) (hb : d290381 q = 1) : d295548 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290381, d295548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290381, d295548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d202307 q = 1) (hb : d290382 q = 1) : d295549 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290382, d295549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290382, d295549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d202307 q = 1) (hb : d290383 q = 1) : d295550 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290383, d295550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290383, d295550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202307 q = 1) (hb : d290390 q = 1) : d295557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290390, d295557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290390, d295557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75909 q ha hb
  have h11 (q : Pattern) (ha : d202307 q = 1) (hb : d290391 q = 1) : d295558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290391, d295558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290391, d295558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d202307 q = 1) (hb : d290392 q = 1) : d295559 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290392, d295559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290392, d295559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d202307 q = 1) (hb : d290393 q = 1) : d295560 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290393, d295560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290393, d295560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d202307 q = 1) (hb : d290394 q = 1) : d295561 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290394, d295561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290394, d295561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d202307 q = 1) (hb : d290395 q = 1) : d295562 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290395, d295562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290395, d295562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75911 (p : Pattern) (ha : d202307 p = 1) (hb : d290401 p = 1) : d295568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290396 q = 1) : d295563 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290396, d295563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290396, d295563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75910 q ha hb
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290397 q = 1) : d295564 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290397, d295564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290397, d295564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290398 q = 1) : d295565 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290398, d295565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290398, d295565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290399 q = 1) : d295566 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290399, d295566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290399, d295566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290400 q = 1) : d295567 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290400, d295567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290400, d295567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290401 q = 1) : d295568 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290401, d295568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290401, d295568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75912 (p : Pattern) (ha : d202307 p = 1) (hb : d290407 p = 1) : d295574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32242 q = 1) (hb : d202307 q = 1) : d293959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32242, d293959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75482 q ha hb
    | true =>
      simp only [d32242, d293959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75483 q ha hb
  have h2 (q : Pattern) (ha : d32243 q = 1) (hb : d202307 q = 1) : d293960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32243, d293960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32243, d293960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32244 q = 1) (hb : d202307 q = 1) : d293961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32244, d293961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32244, d293961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32245 q = 1) (hb : d202307 q = 1) : d293962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32245, d293962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32245, d293962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32246 q = 1) (hb : d202307 q = 1) : d293963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32246, d293963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32246, d293963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290407 q = 1) : d295574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290407, d295574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290407, d295574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro75913 (p : Pattern) (ha : d202307 p = 1) (hb : d290418 p = 1) : d295585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290413 q = 1) : d295580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290413, d295580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75525 q hb ha
    | true =>
      simp only [d290413, d295580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75491 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290414 q = 1) : d295581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290414, d295581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290414, d295581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290415 q = 1) : d295582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290415, d295582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290415, d295582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290416 q = 1) : d295583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290416, d295583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290416, d295583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290417 q = 1) : d295584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290417, d295584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290417, d295584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290418 q = 1) : d295585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290418, d295585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290418, d295585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75914 (p : Pattern) (ha : d202307 p = 1) (hb : d290424 p = 1) : d295591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32248 q = 1) (hb : d202307 q = 1) : d293965 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32248, d293965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75481 q ha hb
    | true =>
      simp only [d32248, d293965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75484 q ha hb
  have h2 (q : Pattern) (ha : d32249 q = 1) (hb : d202307 q = 1) : d293966 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32249, d293966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32249, d293966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290405 q = 1) : d295572 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290405, d295572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290405, d295572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290406 q = 1) : d295573 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290406, d295573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290406, d295573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290408 q = 1) : d295575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290408, d295575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290408, d295575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75912 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290409 q = 1) : d295576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290409, d295576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290409, d295576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d202307 q = 1) (hb : d290410 q = 1) : d295577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290410, d295577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290410, d295577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d202307 q = 1) (hb : d290411 q = 1) : d295578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290411, d295578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290411, d295578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d202307 q = 1) (hb : d290412 q = 1) : d295579 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290412, d295579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290412, d295579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202307 q = 1) (hb : d290419 q = 1) : d295586 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290419, d295586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290419, d295586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75913 q ha hb
  have h11 (q : Pattern) (ha : d202307 q = 1) (hb : d290420 q = 1) : d295587 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290420, d295587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290420, d295587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d202307 q = 1) (hb : d290421 q = 1) : d295588 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290421, d295588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290421, d295588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d202307 q = 1) (hb : d290422 q = 1) : d295589 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290422, d295589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290422, d295589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d202307 q = 1) (hb : d290423 q = 1) : d295590 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290423, d295590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290423, d295590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d202307 q = 1) (hb : d290424 q = 1) : d295591 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290424, d295591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290424, d295591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75915 (p : Pattern) (ha : d202307 p = 1) (hb : d290430 p = 1) : d295597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290425 q = 1) : d295592 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290425, d295592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290425, d295592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75914 q ha hb
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290426 q = 1) : d295593 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290426, d295593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290426, d295593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290427 q = 1) : d295594 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290427, d295594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290427, d295594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290428 q = 1) : d295595 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290428, d295595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290428, d295595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290429 q = 1) : d295596 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290429, d295596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290429, d295596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290430 q = 1) : d295597 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290430, d295597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290430, d295597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75916 (p : Pattern) (ha : d202307 p = 1) (hb : d290437 p = 1) : d295604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32776 q = 1) (hb : d202307 q = 1) : d294242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32776, d294242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75546 q ha hb
    | true =>
      simp only [d32776, d294242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75547 q ha hb
  have h2 (q : Pattern) (ha : d32777 q = 1) (hb : d202307 q = 1) : d294243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32777, d294243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32777, d294243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32778 q = 1) (hb : d202307 q = 1) : d294244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32778, d294244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32778, d294244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32779 q = 1) (hb : d202307 q = 1) : d294245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32779, d294245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32779, d294245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32780 q = 1) (hb : d202307 q = 1) : d294246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32780, d294246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32780, d294246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290437 q = 1) : d295604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290437, d295604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290437, d295604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro75917 (p : Pattern) (ha : d202307 p = 1) (hb : d290448 p = 1) : d295615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290443 q = 1) : d295610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290443, d295610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75586 q hb ha
    | true =>
      simp only [d290443, d295610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75555 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290444 q = 1) : d295611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290444, d295611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290444, d295611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290445 q = 1) : d295612 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290445, d295612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290445, d295612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290446 q = 1) : d295613 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290446, d295613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290446, d295613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290447 q = 1) : d295614 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290447, d295614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290447, d295614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290448 q = 1) : d295615 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290448, d295615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290448, d295615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75918 (p : Pattern) (ha : d202307 p = 1) (hb : d290454 p = 1) : d295621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32782 q = 1) (hb : d202307 q = 1) : d294248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32782, d294248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75545 q ha hb
    | true =>
      simp only [d32782, d294248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75548 q ha hb
  have h2 (q : Pattern) (ha : d32783 q = 1) (hb : d202307 q = 1) : d294249 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32783, d294249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32783, d294249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290435 q = 1) : d295602 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290435, d295602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290435, d295602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290436 q = 1) : d295603 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290436, d295603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290436, d295603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290438 q = 1) : d295605 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290438, d295605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290438, d295605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75916 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290439 q = 1) : d295606 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290439, d295606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290439, d295606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d202307 q = 1) (hb : d290440 q = 1) : d295607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290440, d295607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290440, d295607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d202307 q = 1) (hb : d290441 q = 1) : d295608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290441, d295608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290441, d295608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d202307 q = 1) (hb : d290442 q = 1) : d295609 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290442, d295609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290442, d295609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202307 q = 1) (hb : d290449 q = 1) : d295616 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290449, d295616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290449, d295616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75917 q ha hb
  have h11 (q : Pattern) (ha : d202307 q = 1) (hb : d290450 q = 1) : d295617 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290450, d295617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290450, d295617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d202307 q = 1) (hb : d290451 q = 1) : d295618 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290451, d295618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290451, d295618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d202307 q = 1) (hb : d290452 q = 1) : d295619 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290452, d295619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290452, d295619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d202307 q = 1) (hb : d290453 q = 1) : d295620 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290453, d295620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290453, d295620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d202307 q = 1) (hb : d290454 q = 1) : d295621 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290454, d295621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290454, d295621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro75919 (p : Pattern) (ha : d202307 p = 1) (hb : d290460 p = 1) : d295627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290455 q = 1) : d295622 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290455, d295622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290455, d295622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75918 q ha hb
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290456 q = 1) : d295623 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290456, d295623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290456, d295623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290457 q = 1) : d295624 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290457, d295624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290457, d295624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290458 q = 1) : d295625 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290458, d295625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290458, d295625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290459 q = 1) : d295626 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290459, d295626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290459, d295626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290460 q = 1) : d295627 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290460, d295627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290460, d295627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75920 (p : Pattern) (ha : d202307 p = 1) (hb : d290466 p = 1) : d295633 p = 1 := by
  have h0 (q : Pattern) (ha : d202307 q = 1) (hb : d282120 q = 1) : d207497 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d282120, d207497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75899 q ha hb
    | true =>
      simp only [d282120, d207497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75903 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d282147 q = 1) : d295541 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d282147, d295541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d282147, d295541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75907 q ha hb
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d282148 q = 1) : d295542 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d282148, d295542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282148, d295542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290402 q = 1) : d295569 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290402, d295569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290402, d295569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75911 q ha hb
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290403 q = 1) : d295570 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290403, d295570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290403, d295570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290404 q = 1) : d295571 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290404, d295571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290404, d295571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202307 q = 1) (hb : d290431 q = 1) : d295598 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290431, d295598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290431, d295598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75915 q ha hb
  have h8 (q : Pattern) (ha : d202307 q = 1) (hb : d290432 q = 1) : d295599 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290432, d295599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290432, d295599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202307 q = 1) (hb : d290433 q = 1) : d295600 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290433, d295600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290433, d295600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202307 q = 1) (hb : d290434 q = 1) : d295601 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290434, d295601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290434, d295601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202307 q = 1) (hb : d290461 q = 1) : d295628 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290461, d295628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290461, d295628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75919 q ha hb
  have h12 (q : Pattern) (ha : d202307 q = 1) (hb : d290462 q = 1) : d295629 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290462, d295629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290462, d295629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202307 q = 1) (hb : d290463 q = 1) : d295630 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290463, d295630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290463, d295630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202307 q = 1) (hb : d290464 q = 1) : d295631 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290464, d295631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290464, d295631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202307 q = 1) (hb : d290465 q = 1) : d295632 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d290465, d295632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290465, d295632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202307 q = 1) (hb : d290466 q = 1) : d295633 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d290466, d295633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290466, d295633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro75921 (p : Pattern) (ha : d202307 p = 1) (hb : d290472 p = 1) : d295639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290467 q = 1) : d295634 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d290467, d295634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75920 q ha hb
    | true =>
      simp only [d290467, d295634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290468 q = 1) : d295635 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d290468, d295635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290468, d295635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290469 q = 1) : d295636 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d290469, d295636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290469, d295636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290470 q = 1) : d295637 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d290470, d295637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290470, d295637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290471 q = 1) : d295638 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d290471, d295638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290471, d295638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290472 q = 1) : d295639 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d290472, d295639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290472, d295639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75922 (p : Pattern) (ha : d202307 p = 1) (hb : d290478 p = 1) : d295645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290473 q = 1) : d295640 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d290473, d295640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75921 q ha hb
    | true =>
      simp only [d290473, d295640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290474 q = 1) : d295641 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d290474, d295641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290474, d295641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290475 q = 1) : d295642 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d290475, d295642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290475, d295642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290476 q = 1) : d295643 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d290476, d295643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290476, d295643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290477 q = 1) : d295644 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d290477, d295644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290477, d295644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290478 q = 1) : d295645 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d290478, d295645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290478, d295645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75923 (p : Pattern) (ha : d202307 p = 1) (hb : d290484 p = 1) : d295651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290479 q = 1) : d295646 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d290479, d295646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75922 q ha hb
    | true =>
      simp only [d290479, d295646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290480 q = 1) : d295647 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d290480, d295647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290480, d295647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290481 q = 1) : d295648 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d290481, d295648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290481, d295648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290482 q = 1) : d295649 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d290482, d295649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290482, d295649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290483 q = 1) : d295650 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d290483, d295650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290483, d295650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290484 q = 1) : d295651 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d290484, d295651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290484, d295651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75924 (p : Pattern) (ha : d202307 p = 1) (hb : d290490 p = 1) : d295657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290485 q = 1) : d295652 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d290485, d295652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75923 q ha hb
    | true =>
      simp only [d290485, d295652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290486 q = 1) : d295653 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d290486, d295653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290486, d295653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290487 q = 1) : d295654 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d290487, d295654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290487, d295654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290488 q = 1) : d295655 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d290488, d295655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290488, d295655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290489 q = 1) : d295656 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d290489, d295656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290489, d295656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290490 q = 1) : d295657 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d290490, d295657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290490, d295657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75925 (p : Pattern) (ha : d202307 p = 1) (hb : d290496 p = 1) : d295663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290491 q = 1) : d295658 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d290491, d295658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75924 q ha hb
    | true =>
      simp only [d290491, d295658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290492 q = 1) : d295659 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d290492, d295659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290492, d295659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290493 q = 1) : d295660 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d290493, d295660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290493, d295660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290494 q = 1) : d295661 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d290494, d295661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290494, d295661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290495 q = 1) : d295662 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d290495, d295662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290495, d295662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290496 q = 1) : d295663 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d290496, d295663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290496, d295663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75926 (p : Pattern) (ha : d202307 p = 1) (hb : d290502 p = 1) : d295669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290497 q = 1) : d295664 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d290497, d295664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75925 q ha hb
    | true =>
      simp only [d290497, d295664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290498 q = 1) : d295665 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d290498, d295665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290498, d295665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290499 q = 1) : d295666 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d290499, d295666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290499, d295666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290500 q = 1) : d295667 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d290500, d295667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290500, d295667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290501 q = 1) : d295668 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d290501, d295668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290501, d295668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290502 q = 1) : d295669 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d290502, d295669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290502, d295669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75927 (p : Pattern) (ha : d202307 p = 1) (hb : d290508 p = 1) : d295675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d202307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202307 q = 1) (hb : d290503 q = 1) : d295670 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d290503, d295670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75926 q ha hb
    | true =>
      simp only [d290503, d295670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d202307 q = 1) (hb : d290504 q = 1) : d295671 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d290504, d295671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290504, d295671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d202307 q = 1) (hb : d290505 q = 1) : d295672 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d290505, d295672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290505, d295672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d202307 q = 1) (hb : d290506 q = 1) : d295673 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d290506, d295673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290506, d295673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d202307 q = 1) (hb : d290507 q = 1) : d295674 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d290507, d295674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290507, d295674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d202307 q = 1) (hb : d290508 q = 1) : d295675 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d290508, d295675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290508, d295675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75928 (p : Pattern) (ha : d155083 p = 1) (hb : d205975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155057 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d155078 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d154973 q = 1) (hb : d205913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75605 q ha hb
    | true =>
      simp only [d154973, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155079 q = 1) (hb : d205971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155079, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d155079, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d154974 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d155080 q = 1) (hb : d205972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155080, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155080, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d155081 q = 1) (hb : d205973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155081, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155081, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155082 q = 1) (hb : d205974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155082, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155082, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155083 q = 1) (hb : d205975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155083, d205975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155083, d205975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75929 (p : Pattern) (ha : d155099 p = 1) (hb : d205982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155078 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d154973 q = 1) (hb : d205913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75605 q ha hb
    | true =>
      simp only [d154973, d205913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d155079 q = 1) (hb : d205971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155079, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155079, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d154974 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d155080 q = 1) (hb : d205972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155080, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155080, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d155081 q = 1) (hb : d205973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155081, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155081, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155082 q = 1) (hb : d205974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155082, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155082, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155088 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d155092 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d155094 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d154980 q = 1) (hb : d205920 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75607 q ha hb
    | true =>
      simp only [d154980, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d155095 q = 1) (hb : d205978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155095, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d155095, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d154981 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d155096 q = 1) (hb : d205979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155096, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d155096, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d155097 q = 1) (hb : d205980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155097, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d155097, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155098 q = 1) (hb : d205981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155098, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d155098, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d155099 q = 1) (hb : d205982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155099, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155099, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75930 (p : Pattern) (ha : d155108 p = 1) (hb : d206194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155094 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d154980 q = 1) (hb : d205920 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75607 q ha hb
    | true =>
      simp only [d154980, d205920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155095 q = 1) (hb : d205978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155095, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155095, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d154981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155096 q = 1) (hb : d205979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155096, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155096, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155106 q = 1) (hb : d205980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155106, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155106, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155107 q = 1) (hb : d205981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155107, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155107, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155108 q = 1) (hb : d206194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155108, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155108, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75931 (p : Pattern) (ha : d155137 p = 1) (hb : d206240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155014 q = 1) (hb : d205954 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155014, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75612 q ha hb
    | true =>
      simp only [d155014, d205954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155133 q = 1) (hb : d206236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155133, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155133, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155134 q = 1) (hb : d206237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155134, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155134, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155135 q = 1) (hb : d206238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155135, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155135, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155136 q = 1) (hb : d206239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155136, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155136, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155137 q = 1) (hb : d206240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155137, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155137, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75932 (p : Pattern) (ha : d155143 p = 1) (hb : d207465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155045 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155100 q = 1) (hb : d205983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155100, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75928 q ha hb
    | true =>
      simp only [d155100, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75929 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155102 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155103 q = 1) (hb : d205984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155103, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155103, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155104 q = 1) (hb : d207455 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155104, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155104, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155105 q = 1) (hb : d207456 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155105, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155105, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155109 q = 1) (hb : d206195 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155109, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155109, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75930 q ha hb
  have h8 (q : Pattern) (ha : d155110 q = 1) (hb : d207457 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155110, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155110, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d155111 q = 1) (hb : d207458 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155111, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155111, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d155112 q = 1) (hb : d207459 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155112, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155112, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d155113 q = 1) (hb : d207460 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155113, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155113, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155138 q = 1) (hb : d206241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155138, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155138, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75931 q ha hb
  have h13 (q : Pattern) (ha : d155139 q = 1) (hb : d207461 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155139, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155139, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d155140 q = 1) (hb : d207462 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155140, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155140, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d155141 q = 1) (hb : d207463 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155141, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d155141, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d155142 q = 1) (hb : d207464 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155142, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155142, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d155143 q = 1) (hb : d207465 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155143, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155143, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro75933 (p : Pattern) (ha : d155149 p = 1) (hb : d207471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155030 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155144 q = 1) (hb : d207466 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155144, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155144, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75932 q ha hb
  have h3 (q : Pattern) (ha : d155145 q = 1) (hb : d207467 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155145, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155145, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155146 q = 1) (hb : d207468 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155146, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155146, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155147 q = 1) (hb : d207469 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155147, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155147, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155148 q = 1) (hb : d207470 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155148, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155148, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155149 q = 1) (hb : d207471 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155149, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155149, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro75934 (p : Pattern) (ha : d206096 p = 1) (hb : d292160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155170 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155176 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d292155 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d155078 q = 1) (hb : d206020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75622 q ha hb
    | true =>
      simp only [d155078, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75605 q ha hb
  have h5 (q : Pattern) (ha : d206092 q = 1) (hb : d292156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206092, d292156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206092, d292156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d155211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d206093 q = 1) (hb : d292157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206093, d292157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d206093, d292157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206094 q = 1) (hb : d292158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206094, d292158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206094, d292158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d206095 q = 1) (hb : d292159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206095, d292159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206095, d292159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d206096 q = 1) (hb : d292160 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206096, d292160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206096, d292160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75935 (p : Pattern) (ha : d206103 p = 1) (hb : d292167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155170 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155176 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155078 q = 1) (hb : d206020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75622 q ha hb
    | true =>
      simp only [d155078, d206020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75605 q ha hb
  have h4 (q : Pattern) (ha : d206092 q = 1) (hb : d292156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206092, d292156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206092, d292156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d155211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d206093 q = 1) (hb : d292157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206093, d292157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d206093, d292157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206094 q = 1) (hb : d292158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206094, d292158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206094, d292158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206095 q = 1) (hb : d292159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206095, d292159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206095, d292159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155220 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155224 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d292162 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d155094 q = 1) (hb : d206036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155094, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75626 q ha hb
    | true =>
      simp only [d155094, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75607 q ha hb
  have h13 (q : Pattern) (ha : d206099 q = 1) (hb : d292163 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206099, d292163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d206099, d292163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155230 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d206100 q = 1) (hb : d292164 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206100, d292164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d206100, d292164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d206101 q = 1) (hb : d292165 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206101, d292165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d206101, d292165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d206102 q = 1) (hb : d292166 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206102, d292166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d206102, d292166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d206103 q = 1) (hb : d292167 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206103, d292167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d206103, d292167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75936 (p : Pattern) (ha : d207474 p = 1) (hb : d292174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155094 q = 1) (hb : d206036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155094, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75626 q ha hb
    | true =>
      simp only [d155094, d206036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75607 q ha hb
  have h3 (q : Pattern) (ha : d206099 q = 1) (hb : d292163 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206099, d292163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206099, d292163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155230 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206100 q = 1) (hb : d292164 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206100, d292164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206100, d292164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206101 q = 1) (hb : d292172 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206101, d292172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206101, d292172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206102 q = 1) (hb : d292173 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206102, d292173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206102, d292173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207474 q = 1) (hb : d292174 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207474, d292174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207474, d292174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75937 (p : Pattern) (ha : d207484 p = 1) (hb : d292208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155132 q = 1) (hb : d206074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155132, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75632 q ha hb
    | true =>
      simp only [d155132, d206074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75612 q ha hb
  have h3 (q : Pattern) (ha : d207480 q = 1) (hb : d292204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207480, d292204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207480, d292204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155281 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207481 q = 1) (hb : d292205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207481, d292205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207481, d292205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207482 q = 1) (hb : d292206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207482, d292206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207482, d292206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207483 q = 1) (hb : d292207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207483, d292207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207483, d292207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207484 q = 1) (hb : d292208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207484, d292208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207484, d292208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75938 (p : Pattern) (ha : d207490 p = 1) (hb : d292214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155164 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d206104 q = 1) (hb : d292168 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d206104, d292168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75934 q ha hb
    | true =>
      simp only [d206104, d292168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75935 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155237 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206105 q = 1) (hb : d292169 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d206105, d292169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206105, d292169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207472 q = 1) (hb : d292170 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207472, d292170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207472, d292170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207473 q = 1) (hb : d292171 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207473, d292171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207473, d292171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207475 q = 1) (hb : d292175 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207475, d292175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207475, d292175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75936 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d155246 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d207476 q = 1) (hb : d292176 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207476, d292176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d207476, d292176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207477 q = 1) (hb : d292177 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207477, d292177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207477, d292177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d207478 q = 1) (hb : d292178 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207478, d292178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207478, d292178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d207479 q = 1) (hb : d292179 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207479, d292179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207479, d292179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d207485 q = 1) (hb : d292209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207485, d292209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207485, d292209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75937 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155292 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d207486 q = 1) (hb : d292210 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207486, d292210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207486, d292210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207487 q = 1) (hb : d292211 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207487, d292211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207487, d292211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d207488 q = 1) (hb : d292212 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207488, d292212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d207488, d292212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d207489 q = 1) (hb : d292213 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207489, d292213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d207489, d292213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d207490 q = 1) (hb : d292214 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d207490, d292214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d207490, d292214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75939 (p : Pattern) (ha : d207496 p = 1) (hb : d292220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207491 q = 1) (hb : d292215 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d207491, d292215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207491, d292215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75938 q ha hb
  have h2 (q : Pattern) (ha : d207492 q = 1) (hb : d292216 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d207492, d292216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207492, d292216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d207493 q = 1) (hb : d292217 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d207493, d292217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207493, d292217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207494 q = 1) (hb : d292218 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d207494, d292218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207494, d292218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207495 q = 1) (hb : d292219 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d207495, d292219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207495, d292219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207496 q = 1) (hb : d292220 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d207496, d292220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207496, d292220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75940 (p : Pattern) (ha : d292328 p = 1) (hb : d293465 p = 1) : d294616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d292317 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d292250 q = 1) (hb : d293460 q = 1) : d294611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292250, d293460, d294611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75676 q ha hb
    | true =>
      simp only [d292250, d293460, d294611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75666 q hb ha
  have h5 (q : Pattern) (ha : d292318 q = 1) (hb : d293461 q = 1) : d294612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292318, d293461, d294612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d292318, d293461, d294612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d292324 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d292325 q = 1) (hb : d293462 q = 1) : d294613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292325, d293462, d294613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292325, d293462, d294613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d292326 q = 1) (hb : d293463 q = 1) : d294614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292326, d293463, d294614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d292326, d293463, d294614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292327 q = 1) (hb : d293464 q = 1) : d294615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292327, d293464, d294615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292327, d293464, d294615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292328 q = 1) (hb : d293465 q = 1) : d294616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292328, d293465, d294616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292328, d293465, d294616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75941 (p : Pattern) (ha : d292349 p = 1) (hb : d293474 p = 1) : d294626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d292276 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292250 q = 1) (hb : d293460 q = 1) : d294611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292250, d293460, d294611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75676 q ha hb
    | true =>
      simp only [d292250, d293460, d294611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75666 q hb ha
  have h4 (q : Pattern) (ha : d292318 q = 1) (hb : d293461 q = 1) : d294612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292318, d293461, d294612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d292318, d293461, d294612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d292324 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d292325 q = 1) (hb : d293462 q = 1) : d294613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292325, d293462, d294613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292325, d293462, d294613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d292326 q = 1) (hb : d293463 q = 1) : d294614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292326, d293463, d294614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292326, d293463, d294614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292327 q = 1) (hb : d293464 q = 1) : d294615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292327, d293464, d294615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292327, d293464, d294615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d292334 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d292339 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d292341 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d292260 q = 1) (hb : d293469 q = 1) : d294621 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292260, d293469, d294621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75678 q ha hb
    | true =>
      simp only [d292260, d293469, d294621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75667 q hb ha
  have h13 (q : Pattern) (ha : d292342 q = 1) (hb : d293470 q = 1) : d294622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292342, d293470, d294622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d292342, d293470, d294622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d292345 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d292346 q = 1) (hb : d293471 q = 1) : d294623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292346, d293471, d294623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292346, d293471, d294623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d292347 q = 1) (hb : d293472 q = 1) : d294624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292347, d293472, d294624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d292347, d293472, d294624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d292348 q = 1) (hb : d293473 q = 1) : d294625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292348, d293473, d294625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d292348, d293473, d294625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d292349 q = 1) (hb : d293474 q = 1) : d294626 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292349, d293474, d294626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292349, d293474, d294626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75942 (p : Pattern) (ha : d292369 p = 1) (hb : d295517 p = 1) : d295678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292341 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292260 q = 1) (hb : d293469 q = 1) : d294621 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292260, d293469, d294621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75678 q ha hb
    | true =>
      simp only [d292260, d293469, d294621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75667 q hb ha
  have h3 (q : Pattern) (ha : d292342 q = 1) (hb : d293470 q = 1) : d294622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292342, d293470, d294622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292342, d293470, d294622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d292345 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d292346 q = 1) (hb : d293471 q = 1) : d294623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292346, d293471, d294623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292346, d293471, d294623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d292367 q = 1) (hb : d293472 q = 1) : d294624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292367, d293472, d294624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292367, d293472, d294624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292368 q = 1) (hb : d293473 q = 1) : d294625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292368, d293473, d294625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292368, d293473, d294625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292369 q = 1) (hb : d295517 q = 1) : d295678 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292369, d295517, d295678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292369, d295517, d295678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75943 (p : Pattern) (ha : d292444 p = 1) (hb : d295528 p = 1) : d295689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292433 q = 1) (hb : d295523 q = 1) : d295684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292433, d295523, d295684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75708 q ha hb
    | true =>
      simp only [d292433, d295523, d295684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75672 q hb ha
  have h3 (q : Pattern) (ha : d292434 q = 1) (hb : d295524 q = 1) : d295685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292434, d295524, d295685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292434, d295524, d295685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d292440 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d292441 q = 1) (hb : d295525 q = 1) : d295686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292441, d295525, d295686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292441, d295525, d295686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d292442 q = 1) (hb : d295526 q = 1) : d295687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292442, d295526, d295687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292442, d295526, d295687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292443 q = 1) (hb : d295527 q = 1) : d295688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292443, d295527, d295688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292443, d295527, d295688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292444 q = 1) (hb : d295528 q = 1) : d295689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292444, d295528, d295689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292444, d295528, d295689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75944 (p : Pattern) (ha : d292457 p = 1) (hb : d295534 p = 1) : d295695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d292268 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292350 q = 1) (hb : d293475 q = 1) : d294627 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292350, d293475, d294627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75940 q ha hb
    | true =>
      simp only [d292350, d293475, d294627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75941 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292363 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292364 q = 1) (hb : d293476 q = 1) : d294628 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292364, d293476, d294628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292364, d293476, d294628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d292365 q = 1) (hb : d295515 q = 1) : d295676 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292365, d295515, d295676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292365, d295515, d295676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d292366 q = 1) (hb : d295516 q = 1) : d295677 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292366, d295516, d295677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292366, d295516, d295677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292370 q = 1) (hb : d295518 q = 1) : d295679 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292370, d295518, d295679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d292370, d295518, d295679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75942 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d292372 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d292373 q = 1) (hb : d295519 q = 1) : d295680 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292373, d295519, d295680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292373, d295519, d295680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d292374 q = 1) (hb : d295520 q = 1) : d295681 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292374, d295520, d295681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292374, d295520, d295681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d292375 q = 1) (hb : d295521 q = 1) : d295682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292375, d295521, d295682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292375, d295521, d295682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d292376 q = 1) (hb : d295522 q = 1) : d295683 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292376, d295522, d295683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292376, d295522, d295683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d292445 q = 1) (hb : d295529 q = 1) : d295690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292445, d295529, d295690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d292445, d295529, d295690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75943 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d292452 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d292453 q = 1) (hb : d295530 q = 1) : d295691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292453, d295530, d295691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292453, d295530, d295691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d292454 q = 1) (hb : d295531 q = 1) : d295692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292454, d295531, d295692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292454, d295531, d295692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d292455 q = 1) (hb : d295532 q = 1) : d295693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292455, d295532, d295693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d292455, d295532, d295693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d292456 q = 1) (hb : d295533 q = 1) : d295694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292456, d295533, d295694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d292456, d295533, d295694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d292457 q = 1) (hb : d295534 q = 1) : d295695 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d292457, d295534, d295695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d292457, d295534, d295695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75945 (p : Pattern) (ha : d292463 p = 1) (hb : d295540 p = 1) : d295701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292458 q = 1) (hb : d295535 q = 1) : d295696 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d292458, d295535, d295696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292458, d295535, d295696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75944 q ha hb
  have h2 (q : Pattern) (ha : d292459 q = 1) (hb : d295536 q = 1) : d295697 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d292459, d295536, d295697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292459, d295536, d295697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292460 q = 1) (hb : d295537 q = 1) : d295698 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d292460, d295537, d295698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292460, d295537, d295698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292461 q = 1) (hb : d295538 q = 1) : d295699 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d292461, d295538, d295699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292461, d295538, d295699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292462 q = 1) (hb : d295539 q = 1) : d295700 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d292462, d295539, d295700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292462, d295539, d295700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292463 q = 1) (hb : d295540 q = 1) : d295701 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d292463, d295540, d295701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292463, d295540, d295701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75946 (p : Pattern) (ha : d292599 p = 1) (hb : d293662 p = 1) : d294839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292556 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d292588 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d292521 q = 1) (hb : d293657 q = 1) : d294834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292521, d293657, d294834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75723 q ha hb
    | true =>
      simp only [d292521, d293657, d294834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75724 q ha hb
  have h5 (q : Pattern) (ha : d292589 q = 1) (hb : d293658 q = 1) : d294835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292589, d293658, d294835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d292589, d293658, d294835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d292595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d292596 q = 1) (hb : d293659 q = 1) : d294836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292596, d293659, d294836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292596, d293659, d294836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d292597 q = 1) (hb : d293660 q = 1) : d294837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292597, d293660, d294837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d292597, d293660, d294837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292598 q = 1) (hb : d293661 q = 1) : d294838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292598, d293661, d294838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292598, d293661, d294838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292599 q = 1) (hb : d293662 q = 1) : d294839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292599, d293662, d294839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292599, d293662, d294839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75947 (p : Pattern) (ha : d292620 p = 1) (hb : d293672 p = 1) : d294849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d292547 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292588 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292521 q = 1) (hb : d293657 q = 1) : d294834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292521, d293657, d294834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75723 q ha hb
    | true =>
      simp only [d292521, d293657, d294834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75724 q ha hb
  have h4 (q : Pattern) (ha : d292589 q = 1) (hb : d293658 q = 1) : d294835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292589, d293658, d294835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d292589, d293658, d294835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d292595 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d292596 q = 1) (hb : d293659 q = 1) : d294836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292596, d293659, d294836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292596, d293659, d294836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d292597 q = 1) (hb : d293660 q = 1) : d294837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292597, d293660, d294837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292597, d293660, d294837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292598 q = 1) (hb : d293661 q = 1) : d294838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292598, d293661, d294838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292598, d293661, d294838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d292605 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d292610 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d292612 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d292531 q = 1) (hb : d293667 q = 1) : d294844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292531, d293667, d294844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75726 q ha hb
    | true =>
      simp only [d292531, d293667, d294844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75727 q ha hb
  have h13 (q : Pattern) (ha : d292613 q = 1) (hb : d293668 q = 1) : d294845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292613, d293668, d294845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d292613, d293668, d294845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d292616 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d292617 q = 1) (hb : d293669 q = 1) : d294846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292617, d293669, d294846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292617, d293669, d294846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d292618 q = 1) (hb : d293670 q = 1) : d294847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292618, d293670, d294847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d292618, d293670, d294847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d292619 q = 1) (hb : d293671 q = 1) : d294848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292619, d293671, d294848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d292619, d293671, d294848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d292620 q = 1) (hb : d293672 q = 1) : d294849 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292620, d293672, d294849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292620, d293672, d294849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75948 (p : Pattern) (ha : d292640 p = 1) (hb : d295545 p = 1) : d295706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292531 q = 1) (hb : d293667 q = 1) : d294844 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292531, d293667, d294844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75726 q ha hb
    | true =>
      simp only [d292531, d293667, d294844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75727 q ha hb
  have h3 (q : Pattern) (ha : d292613 q = 1) (hb : d293668 q = 1) : d294845 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292613, d293668, d294845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292613, d293668, d294845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d292616 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d292617 q = 1) (hb : d293669 q = 1) : d294846 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292617, d293669, d294846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292617, d293669, d294846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d292638 q = 1) (hb : d293670 q = 1) : d294847 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292638, d293670, d294847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292638, d293670, d294847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292639 q = 1) (hb : d293671 q = 1) : d294848 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292639, d293671, d294848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292639, d293671, d294848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292640 q = 1) (hb : d295545 q = 1) : d295706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292640, d295545, d295706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292640, d295545, d295706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75949 (p : Pattern) (ha : d292734 p = 1) (hb : d295556 p = 1) : d295717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292718 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292723 q = 1) (hb : d295551 q = 1) : d295712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292723, d295551, d295712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75763 q ha hb
    | true =>
      simp only [d292723, d295551, d295712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75766 q ha hb
  have h3 (q : Pattern) (ha : d292724 q = 1) (hb : d295552 q = 1) : d295713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292724, d295552, d295713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292724, d295552, d295713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d292730 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d292731 q = 1) (hb : d295553 q = 1) : d295714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292731, d295553, d295714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292731, d295553, d295714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d292732 q = 1) (hb : d295554 q = 1) : d295715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292732, d295554, d295715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292732, d295554, d295715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292733 q = 1) (hb : d295555 q = 1) : d295716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292733, d295555, d295716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292733, d295555, d295716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292734 q = 1) (hb : d295556 q = 1) : d295717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292734, d295556, d295717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292734, d295556, d295717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75950 (p : Pattern) (ha : d292747 p = 1) (hb : d295562 p = 1) : d295723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d292539 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292621 q = 1) (hb : d293673 q = 1) : d294850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292621, d293673, d294850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75946 q ha hb
    | true =>
      simp only [d292621, d293673, d294850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75947 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292634 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292635 q = 1) (hb : d293674 q = 1) : d294851 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292635, d293674, d294851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292635, d293674, d294851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d292636 q = 1) (hb : d295543 q = 1) : d295704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292636, d295543, d295704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292636, d295543, d295704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d292637 q = 1) (hb : d295544 q = 1) : d295705 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292637, d295544, d295705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292637, d295544, d295705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292641 q = 1) (hb : d295546 q = 1) : d295707 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292641, d295546, d295707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d292641, d295546, d295707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75948 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d292643 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d292644 q = 1) (hb : d295547 q = 1) : d295708 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292644, d295547, d295708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292644, d295547, d295708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d292645 q = 1) (hb : d295548 q = 1) : d295709 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292645, d295548, d295709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292645, d295548, d295709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d292646 q = 1) (hb : d295549 q = 1) : d295710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292646, d295549, d295710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292646, d295549, d295710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d292647 q = 1) (hb : d295550 q = 1) : d295711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292647, d295550, d295711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292647, d295550, d295711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d292735 q = 1) (hb : d295557 q = 1) : d295718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292735, d295557, d295718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d292735, d295557, d295718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75949 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d292742 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d292743 q = 1) (hb : d295558 q = 1) : d295719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292743, d295558, d295719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292743, d295558, d295719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d292744 q = 1) (hb : d295559 q = 1) : d295720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292744, d295559, d295720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d292744, d295559, d295720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d292745 q = 1) (hb : d295560 q = 1) : d295721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292745, d295560, d295721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d292745, d295560, d295721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d292746 q = 1) (hb : d295561 q = 1) : d295722 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292746, d295561, d295722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d292746, d295561, d295722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d292747 q = 1) (hb : d295562 q = 1) : d295723 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d292747, d295562, d295723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d292747, d295562, d295723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75951 (p : Pattern) (ha : d292753 p = 1) (hb : d295568 p = 1) : d295729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292748 q = 1) (hb : d295563 q = 1) : d295724 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d292748, d295563, d295724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292748, d295563, d295724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75950 q ha hb
  have h2 (q : Pattern) (ha : d292749 q = 1) (hb : d295564 q = 1) : d295725 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d292749, d295564, d295725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292749, d295564, d295725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d292750 q = 1) (hb : d295565 q = 1) : d295726 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d292750, d295565, d295726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292750, d295565, d295726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292751 q = 1) (hb : d295566 q = 1) : d295727 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d292751, d295566, d295727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292751, d295566, d295727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d292752 q = 1) (hb : d295567 q = 1) : d295728 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d292752, d295567, d295728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292752, d295567, d295728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292753 q = 1) (hb : d295568 q = 1) : d295729 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d292753, d295568, d295729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292753, d295568, d295729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75952 (p : Pattern) (ha : d292900 p = 1) (hb : d293954 p = 1) : d295064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292838 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292847 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d292872 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d292812 q = 1) (hb : d293949 q = 1) : d295059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75780 q ha hb
    | true =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75781 q ha hb
  have h5 (q : Pattern) (ha : d292873 q = 1) (hb : d293950 q = 1) : d295060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292873, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d292873, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d292896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d292897 q = 1) (hb : d293951 q = 1) : d295061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292897, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d292897, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d292898 q = 1) (hb : d293952 q = 1) : d295062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292898, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d292898, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d292899 q = 1) (hb : d293953 q = 1) : d295063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292899, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292899, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d292900 q = 1) (hb : d293954 q = 1) : d295064 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292900, d293954, d295064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292900, d293954, d295064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75953 (p : Pattern) (ha : d292921 p = 1) (hb : d293964 p = 1) : d295074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d292838 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292847 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292872 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292812 q = 1) (hb : d293949 q = 1) : d295059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75780 q ha hb
    | true =>
      simp only [d292812, d293949, d295059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75781 q ha hb
  have h4 (q : Pattern) (ha : d292873 q = 1) (hb : d293950 q = 1) : d295060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292873, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d292873, d293950, d295060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d292896 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d292897 q = 1) (hb : d293951 q = 1) : d295061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292897, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d292897, d293951, d295061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d292898 q = 1) (hb : d293952 q = 1) : d295062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292898, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292898, d293952, d295062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292899 q = 1) (hb : d293953 q = 1) : d295063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292899, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292899, d293953, d295063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d292906 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d292911 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d292913 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d292822 q = 1) (hb : d293959 q = 1) : d295069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292822, d293959, d295069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75783 q ha hb
    | true =>
      simp only [d292822, d293959, d295069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75784 q ha hb
  have h13 (q : Pattern) (ha : d292914 q = 1) (hb : d293960 q = 1) : d295070 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292914, d293960, d295070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d292914, d293960, d295070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d292917 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d292918 q = 1) (hb : d293961 q = 1) : d295071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292918, d293961, d295071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d292918, d293961, d295071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d292919 q = 1) (hb : d293962 q = 1) : d295072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292919, d293962, d295072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d292919, d293962, d295072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d292920 q = 1) (hb : d293963 q = 1) : d295073 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292920, d293963, d295073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d292920, d293963, d295073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d292921 q = 1) (hb : d293964 q = 1) : d295074 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292921, d293964, d295074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d292921, d293964, d295074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75954 (p : Pattern) (ha : d292941 p = 1) (hb : d295574 p = 1) : d295735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d292913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292822 q = 1) (hb : d293959 q = 1) : d295069 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d292822, d293959, d295069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75783 q ha hb
    | true =>
      simp only [d292822, d293959, d295069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75784 q ha hb
  have h3 (q : Pattern) (ha : d292914 q = 1) (hb : d293960 q = 1) : d295070 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d292914, d293960, d295070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292914, d293960, d295070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d292917 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d292918 q = 1) (hb : d293961 q = 1) : d295071 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d292918, d293961, d295071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292918, d293961, d295071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d292939 q = 1) (hb : d293962 q = 1) : d295072 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d292939, d293962, d295072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292939, d293962, d295072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292940 q = 1) (hb : d293963 q = 1) : d295073 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d292940, d293963, d295073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292940, d293963, d295073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d292941 q = 1) (hb : d295574 q = 1) : d295735 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d292941, d295574, d295735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292941, d295574, d295735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75955 (p : Pattern) (ha : d293045 p = 1) (hb : d295585 p = 1) : d295746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d293014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d293019 q = 1) (hb : d295580 q = 1) : d295741 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293019, d295580, d295741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75821 q ha hb
    | true =>
      simp only [d293019, d295580, d295741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75827 q ha hb
  have h3 (q : Pattern) (ha : d293020 q = 1) (hb : d295581 q = 1) : d295742 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293020, d295581, d295742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293020, d295581, d295742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d293041 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293042 q = 1) (hb : d295582 q = 1) : d295743 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293042, d295582, d295743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293042, d295582, d295743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d293043 q = 1) (hb : d295583 q = 1) : d295744 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293043, d295583, d295744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293043, d295583, d295744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293044 q = 1) (hb : d295584 q = 1) : d295745 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293044, d295584, d295745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293044, d295584, d295745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293045 q = 1) (hb : d295585 q = 1) : d295746 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293045, d295585, d295746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293045, d295585, d295746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75956 (p : Pattern) (ha : d293058 p = 1) (hb : d295591 p = 1) : d295752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d292830 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292922 q = 1) (hb : d293965 q = 1) : d295075 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292922, d293965, d295075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75952 q ha hb
    | true =>
      simp only [d292922, d293965, d295075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75953 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d292935 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d292936 q = 1) (hb : d293966 q = 1) : d295076 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292936, d293966, d295076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d292936, d293966, d295076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d292937 q = 1) (hb : d295572 q = 1) : d295733 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292937, d295572, d295733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292937, d295572, d295733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d292938 q = 1) (hb : d295573 q = 1) : d295734 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292938, d295573, d295734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292938, d295573, d295734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d292942 q = 1) (hb : d295575 q = 1) : d295736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292942, d295575, d295736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d292942, d295575, d295736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75954 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d292944 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d292945 q = 1) (hb : d295576 q = 1) : d295737 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d292945, d295576, d295737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d292945, d295576, d295737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d292946 q = 1) (hb : d295577 q = 1) : d295738 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d292946, d295577, d295738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d292946, d295577, d295738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d292947 q = 1) (hb : d295578 q = 1) : d295739 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d292947, d295578, d295739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d292947, d295578, d295739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d292948 q = 1) (hb : d295579 q = 1) : d295740 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d292948, d295579, d295740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d292948, d295579, d295740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293046 q = 1) (hb : d295586 q = 1) : d295747 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293046, d295586, d295747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d293046, d295586, d295747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75955 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d293053 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d293054 q = 1) (hb : d295587 q = 1) : d295748 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293054, d295587, d295748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293054, d295587, d295748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d293055 q = 1) (hb : d295588 q = 1) : d295749 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293055, d295588, d295749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d293055, d295588, d295749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d293056 q = 1) (hb : d295589 q = 1) : d295750 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d293056, d295589, d295750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d293056, d295589, d295750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d293057 q = 1) (hb : d295590 q = 1) : d295751 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d293057, d295590, d295751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d293057, d295590, d295751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d293058 q = 1) (hb : d295591 q = 1) : d295752 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d293058, d295591, d295752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d293058, d295591, d295752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75957 (p : Pattern) (ha : d293064 p = 1) (hb : d295597 p = 1) : d295758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293059 q = 1) (hb : d295592 q = 1) : d295753 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d293059, d295592, d295753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293059, d295592, d295753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75956 q ha hb
  have h2 (q : Pattern) (ha : d293060 q = 1) (hb : d295593 q = 1) : d295754 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d293060, d295593, d295754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293060, d295593, d295754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293061 q = 1) (hb : d295594 q = 1) : d295755 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d293061, d295594, d295755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293061, d295594, d295755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293062 q = 1) (hb : d295595 q = 1) : d295756 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d293062, d295595, d295756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293062, d295595, d295756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293063 q = 1) (hb : d295596 q = 1) : d295757 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d293063, d295596, d295757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293063, d295596, d295757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293064 q = 1) (hb : d295597 q = 1) : d295758 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d293064, d295597, d295758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293064, d295597, d295758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75958 (p : Pattern) (ha : d293180 p = 1) (hb : d294237 p = 1) : d295275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d293137 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293146 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d293160 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d293111 q = 1) (hb : d294232 q = 1) : d295270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75838 q ha hb
    | true =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75839 q ha hb
  have h5 (q : Pattern) (ha : d293161 q = 1) (hb : d294233 q = 1) : d295271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293161, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d293161, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d293176 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d293177 q = 1) (hb : d294234 q = 1) : d295272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293177, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293177, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d293178 q = 1) (hb : d294235 q = 1) : d295273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293178, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d293178, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293179 q = 1) (hb : d294236 q = 1) : d295274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293179, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293179, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293180 q = 1) (hb : d294237 q = 1) : d295275 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293180, d294237, d295275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293180, d294237, d295275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75959 (p : Pattern) (ha : d293201 p = 1) (hb : d294247 p = 1) : d295285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d293137 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d293146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293160 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293111 q = 1) (hb : d294232 q = 1) : d295270 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75838 q ha hb
    | true =>
      simp only [d293111, d294232, d295270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75839 q ha hb
  have h4 (q : Pattern) (ha : d293161 q = 1) (hb : d294233 q = 1) : d295271 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293161, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d293161, d294233, d295271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d293176 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d293177 q = 1) (hb : d294234 q = 1) : d295272 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293177, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293177, d294234, d295272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d293178 q = 1) (hb : d294235 q = 1) : d295273 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293178, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293178, d294235, d295273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293179 q = 1) (hb : d294236 q = 1) : d295274 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293179, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293179, d294236, d295274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d293186 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d293191 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d293193 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d293121 q = 1) (hb : d294242 q = 1) : d295280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293121, d294242, d295280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75841 q ha hb
    | true =>
      simp only [d293121, d294242, d295280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75842 q ha hb
  have h13 (q : Pattern) (ha : d293194 q = 1) (hb : d294243 q = 1) : d295281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293194, d294243, d295281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d293194, d294243, d295281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d293197 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d293198 q = 1) (hb : d294244 q = 1) : d295282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293198, d294244, d295282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293198, d294244, d295282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d293199 q = 1) (hb : d294245 q = 1) : d295283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293199, d294245, d295283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d293199, d294245, d295283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d293200 q = 1) (hb : d294246 q = 1) : d295284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293200, d294246, d295284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d293200, d294246, d295284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d293201 q = 1) (hb : d294247 q = 1) : d295285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293201, d294247, d295285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293201, d294247, d295285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75960 (p : Pattern) (ha : d293221 p = 1) (hb : d295604 p = 1) : d295765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d293193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d293121 q = 1) (hb : d294242 q = 1) : d295280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293121, d294242, d295280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75841 q ha hb
    | true =>
      simp only [d293121, d294242, d295280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75842 q ha hb
  have h3 (q : Pattern) (ha : d293194 q = 1) (hb : d294243 q = 1) : d295281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293194, d294243, d295281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293194, d294243, d295281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d293197 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293198 q = 1) (hb : d294244 q = 1) : d295282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293198, d294244, d295282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293198, d294244, d295282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d293219 q = 1) (hb : d294245 q = 1) : d295283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293219, d294245, d295283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293219, d294245, d295283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293220 q = 1) (hb : d294246 q = 1) : d295284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293220, d294246, d295284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293220, d294246, d295284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293221 q = 1) (hb : d295604 q = 1) : d295765 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293221, d295604, d295765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293221, d295604, d295765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75961 (p : Pattern) (ha : d293301 p = 1) (hb : d295615 p = 1) : d295776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d293276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d293281 q = 1) (hb : d295610 q = 1) : d295771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d293281, d295610, d295771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75878 q ha hb
    | true =>
      simp only [d293281, d295610, d295771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75884 q ha hb
  have h3 (q : Pattern) (ha : d293282 q = 1) (hb : d295611 q = 1) : d295772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293282, d295611, d295772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293282, d295611, d295772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d293297 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293298 q = 1) (hb : d295612 q = 1) : d295773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293298, d295612, d295773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293298, d295612, d295773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d293299 q = 1) (hb : d295613 q = 1) : d295774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293299, d295613, d295774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293299, d295613, d295774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293300 q = 1) (hb : d295614 q = 1) : d295775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293300, d295614, d295775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293300, d295614, d295775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293301 q = 1) (hb : d295615 q = 1) : d295776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293301, d295615, d295776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293301, d295615, d295776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75962 (p : Pattern) (ha : d293314 p = 1) (hb : d295621 p = 1) : d295782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d293129 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293202 q = 1) (hb : d294248 q = 1) : d295286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293202, d294248, d295286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75958 q ha hb
    | true =>
      simp only [d293202, d294248, d295286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75959 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293215 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293216 q = 1) (hb : d294249 q = 1) : d295287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293216, d294249, d295287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293216, d294249, d295287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293217 q = 1) (hb : d295602 q = 1) : d295763 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293217, d295602, d295763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293217, d295602, d295763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d293218 q = 1) (hb : d295603 q = 1) : d295764 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d293218, d295603, d295764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293218, d295603, d295764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293222 q = 1) (hb : d295605 q = 1) : d295766 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293222, d295605, d295766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d293222, d295605, d295766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75960 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d293224 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d293225 q = 1) (hb : d295606 q = 1) : d295767 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293225, d295606, d295767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d293225, d295606, d295767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d293226 q = 1) (hb : d295607 q = 1) : d295768 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293226, d295607, d295768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293226, d295607, d295768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d293227 q = 1) (hb : d295608 q = 1) : d295769 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d293227, d295608, d295769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293227, d295608, d295769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d293228 q = 1) (hb : d295609 q = 1) : d295770 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d293228, d295609, d295770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293228, d295609, d295770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293302 q = 1) (hb : d295616 q = 1) : d295777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293302, d295616, d295777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d293302, d295616, d295777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75961 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d293309 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d293310 q = 1) (hb : d295617 q = 1) : d295778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293310, d295617, d295778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293310, d295617, d295778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d293311 q = 1) (hb : d295618 q = 1) : d295779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d293311, d295618, d295779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d293311, d295618, d295779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d293312 q = 1) (hb : d295619 q = 1) : d295780 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d293312, d295619, d295780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d293312, d295619, d295780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d293313 q = 1) (hb : d295620 q = 1) : d295781 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d293313, d295620, d295781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d293313, d295620, d295781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d293314 q = 1) (hb : d295621 q = 1) : d295782 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d293314, d295621, d295782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d293314, d295621, d295782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75963 (p : Pattern) (ha : d293320 p = 1) (hb : d295627 p = 1) : d295788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293315 q = 1) (hb : d295622 q = 1) : d295783 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d293315, d295622, d295783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293315, d295622, d295783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75962 q ha hb
  have h2 (q : Pattern) (ha : d293316 q = 1) (hb : d295623 q = 1) : d295784 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d293316, d295623, d295784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293316, d295623, d295784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d293317 q = 1) (hb : d295624 q = 1) : d295785 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d293317, d295624, d295785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293317, d295624, d295785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d293318 q = 1) (hb : d295625 q = 1) : d295786 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d293318, d295625, d295786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293318, d295625, d295786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d293319 q = 1) (hb : d295626 q = 1) : d295787 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d293319, d295626, d295787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293319, d295626, d295787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293320 q = 1) (hb : d295627 q = 1) : d295788 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d293320, d295627, d295788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d293320, d295627, d295788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75964 (p : Pattern) (ha : d293326 p = 1) (hb : d295633 p = 1) : d295794 p = 1 := by
  have h0 (q : Pattern) (ha : d207497 q = 1) (hb : d292221 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d207497, d292221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75933 q hb ha
    | true =>
      simp only [d207497, d292221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75939 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d292464 q = 1) (hb : d295541 q = 1) : d295702 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d292464, d295541, d295702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292464, d295541, d295702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75945 q ha hb
  have h3 (q : Pattern) (ha : d292465 q = 1) (hb : d295542 q = 1) : d295703 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d292465, d295542, d295703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d292465, d295542, d295703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292754 q = 1) (hb : d295569 q = 1) : d295730 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d292754, d295569, d295730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292754, d295569, d295730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75951 q ha hb
  have h5 (q : Pattern) (ha : d292755 q = 1) (hb : d295570 q = 1) : d295731 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d292755, d295570, d295731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d292755, d295570, d295731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d292756 q = 1) (hb : d295571 q = 1) : d295732 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d292756, d295571, d295732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d292756, d295571, d295732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293065 q = 1) (hb : d295598 q = 1) : d295759 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d293065, d295598, d295759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293065, d295598, d295759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75957 q ha hb
  have h8 (q : Pattern) (ha : d293066 q = 1) (hb : d295599 q = 1) : d295760 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d293066, d295599, d295760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293066, d295599, d295760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293067 q = 1) (hb : d295600 q = 1) : d295761 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d293067, d295600, d295761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293067, d295600, d295761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293068 q = 1) (hb : d295601 q = 1) : d295762 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d293068, d295601, d295762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d293068, d295601, d295762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d293321 q = 1) (hb : d295628 q = 1) : d295789 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d293321, d295628, d295789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293321, d295628, d295789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75963 q ha hb
  have h12 (q : Pattern) (ha : d293322 q = 1) (hb : d295629 q = 1) : d295790 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d293322, d295629, d295790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293322, d295629, d295790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d293323 q = 1) (hb : d295630 q = 1) : d295791 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d293323, d295630, d295791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293323, d295630, d295791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d293324 q = 1) (hb : d295631 q = 1) : d295792 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d293324, d295631, d295792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d293324, d295631, d295792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d293325 q = 1) (hb : d295632 q = 1) : d295793 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d293325, d295632, d295793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293325, d295632, d295793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293326 q = 1) (hb : d295633 q = 1) : d295794 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d293326, d295633, d295794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d293326, d295633, d295794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro75965 (p : Pattern) (ha : d293332 p = 1) (hb : d295639 p = 1) : d295800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293327 q = 1) (hb : d295634 q = 1) : d295795 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d293327, d295634, d295795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75964 q ha hb
    | true =>
      simp only [d293327, d295634, d295795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293328 q = 1) (hb : d295635 q = 1) : d295796 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d293328, d295635, d295796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293328, d295635, d295796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293329 q = 1) (hb : d295636 q = 1) : d295797 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d293329, d295636, d295797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293329, d295636, d295797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293330 q = 1) (hb : d295637 q = 1) : d295798 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d293330, d295637, d295798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293330, d295637, d295798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293331 q = 1) (hb : d295638 q = 1) : d295799 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d293331, d295638, d295799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293331, d295638, d295799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293332 q = 1) (hb : d295639 q = 1) : d295800 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d293332, d295639, d295800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293332, d295639, d295800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75966 (p : Pattern) (ha : d293338 p = 1) (hb : d295645 p = 1) : d295806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293333 q = 1) (hb : d295640 q = 1) : d295801 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d293333, d295640, d295801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75965 q ha hb
    | true =>
      simp only [d293333, d295640, d295801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293334 q = 1) (hb : d295641 q = 1) : d295802 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d293334, d295641, d295802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293334, d295641, d295802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293335 q = 1) (hb : d295642 q = 1) : d295803 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d293335, d295642, d295803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293335, d295642, d295803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293336 q = 1) (hb : d295643 q = 1) : d295804 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d293336, d295643, d295804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293336, d295643, d295804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293337 q = 1) (hb : d295644 q = 1) : d295805 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d293337, d295644, d295805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293337, d295644, d295805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293338 q = 1) (hb : d295645 q = 1) : d295806 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d293338, d295645, d295806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293338, d295645, d295806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75967 (p : Pattern) (ha : d293344 p = 1) (hb : d295651 p = 1) : d295812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293339 q = 1) (hb : d295646 q = 1) : d295807 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d293339, d295646, d295807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75966 q ha hb
    | true =>
      simp only [d293339, d295646, d295807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293340 q = 1) (hb : d295647 q = 1) : d295808 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d293340, d295647, d295808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293340, d295647, d295808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293341 q = 1) (hb : d295648 q = 1) : d295809 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d293341, d295648, d295809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293341, d295648, d295809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293342 q = 1) (hb : d295649 q = 1) : d295810 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d293342, d295649, d295810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293342, d295649, d295810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293343 q = 1) (hb : d295650 q = 1) : d295811 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d293343, d295650, d295811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293343, d295650, d295811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293344 q = 1) (hb : d295651 q = 1) : d295812 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d293344, d295651, d295812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293344, d295651, d295812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75968 (p : Pattern) (ha : d293350 p = 1) (hb : d295657 p = 1) : d295818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293345 q = 1) (hb : d295652 q = 1) : d295813 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d293345, d295652, d295813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75967 q ha hb
    | true =>
      simp only [d293345, d295652, d295813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293346 q = 1) (hb : d295653 q = 1) : d295814 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d293346, d295653, d295814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293346, d295653, d295814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293347 q = 1) (hb : d295654 q = 1) : d295815 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d293347, d295654, d295815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293347, d295654, d295815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293348 q = 1) (hb : d295655 q = 1) : d295816 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d293348, d295655, d295816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293348, d295655, d295816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293349 q = 1) (hb : d295656 q = 1) : d295817 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d293349, d295656, d295817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293349, d295656, d295817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293350 q = 1) (hb : d295657 q = 1) : d295818 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d293350, d295657, d295818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293350, d295657, d295818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75969 (p : Pattern) (ha : d293356 p = 1) (hb : d295663 p = 1) : d295824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293351 q = 1) (hb : d295658 q = 1) : d295819 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d293351, d295658, d295819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75968 q ha hb
    | true =>
      simp only [d293351, d295658, d295819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293352 q = 1) (hb : d295659 q = 1) : d295820 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d293352, d295659, d295820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293352, d295659, d295820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293353 q = 1) (hb : d295660 q = 1) : d295821 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d293353, d295660, d295821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293353, d295660, d295821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293354 q = 1) (hb : d295661 q = 1) : d295822 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d293354, d295661, d295822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293354, d295661, d295822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293355 q = 1) (hb : d295662 q = 1) : d295823 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d293355, d295662, d295823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293355, d295662, d295823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293356 q = 1) (hb : d295663 q = 1) : d295824 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d293356, d295663, d295824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293356, d295663, d295824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75970 (p : Pattern) (ha : d293362 p = 1) (hb : d295669 p = 1) : d295830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293357 q = 1) (hb : d295664 q = 1) : d295825 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d293357, d295664, d295825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75969 q ha hb
    | true =>
      simp only [d293357, d295664, d295825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293358 q = 1) (hb : d295665 q = 1) : d295826 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d293358, d295665, d295826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293358, d295665, d295826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293359 q = 1) (hb : d295666 q = 1) : d295827 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d293359, d295666, d295827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293359, d295666, d295827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293360 q = 1) (hb : d295667 q = 1) : d295828 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d293360, d295667, d295828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293360, d295667, d295828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293361 q = 1) (hb : d295668 q = 1) : d295829 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d293361, d295668, d295829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293361, d295668, d295829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293362 q = 1) (hb : d295669 q = 1) : d295830 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d293362, d295669, d295830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293362, d295669, d295830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75971 (p : Pattern) (ha : d293368 p = 1) (hb : d295675 p = 1) : d295836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293363 q = 1) (hb : d295670 q = 1) : d295831 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d293363, d295670, d295831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75970 q ha hb
    | true =>
      simp only [d293363, d295670, d295831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d293364 q = 1) (hb : d295671 q = 1) : d295832 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d293364, d295671, d295832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293364, d295671, d295832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d293365 q = 1) (hb : d295672 q = 1) : d295833 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d293365, d295672, d295833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293365, d295672, d295833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d293366 q = 1) (hb : d295673 q = 1) : d295834 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d293366, d295673, d295834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293366, d295673, d295834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d293367 q = 1) (hb : d295674 q = 1) : d295835 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d293367, d295674, d295835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293367, d295674, d295835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d293368 q = 1) (hb : d295675 q = 1) : d295836 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d293368, d295675, d295836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293368, d295675, d295836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro75972 (p : Pattern) (ha : d158248 p = 1) (hb : d205975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152960 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152981 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d205913 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158244 q = 1) (hb : d205971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158244, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d158244, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152877 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d158245 q = 1) (hb : d205972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158245, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d158245, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d158246 q = 1) (hb : d205973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158246, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d158246, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d158247 q = 1) (hb : d205974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158247, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d158247, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158248 q = 1) (hb : d205975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158248, d205975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158248, d205975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75973 (p : Pattern) (ha : d158253 p = 1) (hb : d205982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152954 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152960 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d205913 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d158244 q = 1) (hb : d205971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158244, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d158244, d205971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d152877 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d158245 q = 1) (hb : d205972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158245, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158245, d205972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d158246 q = 1) (hb : d205973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158246, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d158246, d205973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158247 q = 1) (hb : d205974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158247, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d158247, d205974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d153012 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d153016 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d153018 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d205920 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d158249 q = 1) (hb : d205978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158249, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d158249, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d152884 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d158250 q = 1) (hb : d205979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158250, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158250, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d158251 q = 1) (hb : d205980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158251, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d158251, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d158252 q = 1) (hb : d205981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158252, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d158252, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d158253 q = 1) (hb : d205982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158253, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d158253, d205982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75974 (p : Pattern) (ha : d158260 p = 1) (hb : d206194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153018 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205920 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158249 q = 1) (hb : d205978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158249, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d158249, d205978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152884 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158250 q = 1) (hb : d205979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158250, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158250, d205979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d158258 q = 1) (hb : d205980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158258, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158258, d205980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158259 q = 1) (hb : d205981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158259, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158259, d205981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158260 q = 1) (hb : d206194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158260, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158260, d206194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75975 (p : Pattern) (ha : d158270 p = 1) (hb : d206240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153058 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d205954 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158266 q = 1) (hb : d206236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158266, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d158266, d206236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152918 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158267 q = 1) (hb : d206237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158267, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158267, d206237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d158268 q = 1) (hb : d206238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158268, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158268, d206238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158269 q = 1) (hb : d206239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158269, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158269, d206239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158270 q = 1) (hb : d206240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158270, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158270, d206240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75976 (p : Pattern) (ha : d158276 p = 1) (hb : d207465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158254 q = 1) (hb : d205983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158254, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75972 q ha hb
    | true =>
      simp only [d158254, d205983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75973 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153028 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158255 q = 1) (hb : d205984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158255, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158255, d205984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158256 q = 1) (hb : d207455 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158256, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158256, d207455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158257 q = 1) (hb : d207456 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158257, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d158257, d207456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158261 q = 1) (hb : d206195 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158261, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158261, d206195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75974 q ha hb
  have h8 (q : Pattern) (ha : d158262 q = 1) (hb : d207457 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158262, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158262, d207457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d158263 q = 1) (hb : d207458 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158263, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d158263, d207458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d158264 q = 1) (hb : d207459 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158264, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158264, d207459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158265 q = 1) (hb : d207460 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158265, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158265, d207460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d158271 q = 1) (hb : d206241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158271, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158271, d206241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75975 q ha hb
  have h13 (q : Pattern) (ha : d158272 q = 1) (hb : d207461 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158272, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158272, d207461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d158273 q = 1) (hb : d207462 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158273, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158273, d207462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d158274 q = 1) (hb : d207463 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158274, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d158274, d207463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d158275 q = 1) (hb : d207464 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158275, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158275, d207464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158276 q = 1) (hb : d207465 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158276, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d158276, d207465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro75977 (p : Pattern) (ha : d158282 p = 1) (hb : d207471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152933 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d158277 q = 1) (hb : d207466 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158277, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158277, d207466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75976 q ha hb
  have h3 (q : Pattern) (ha : d158278 q = 1) (hb : d207467 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158278, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158278, d207467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158279 q = 1) (hb : d207468 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158279, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158279, d207468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158280 q = 1) (hb : d207469 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158280, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158280, d207469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158281 q = 1) (hb : d207470 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158281, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158281, d207470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158282 q = 1) (hb : d207471 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158282, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d158282, d207471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro75978 (p : Pattern) (ha : d206096 p = 1) (hb : d295841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d290536 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d206020 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206092 q = 1) (hb : d295837 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206092, d295837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206092, d295837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d153177 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d206093 q = 1) (hb : d295838 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206093, d295838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d206093, d295838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206094 q = 1) (hb : d295839 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206094, d295839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206094, d295839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d206095 q = 1) (hb : d295840 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206095, d295840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206095, d295840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d206096 q = 1) (hb : d295841 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206096, d295841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206096, d295841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75979 (p : Pattern) (ha : d206103 p = 1) (hb : d295846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d153115 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290536 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d206020 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d206092 q = 1) (hb : d295837 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206092, d295837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d206092, d295837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d153177 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d206093 q = 1) (hb : d295838 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206093, d295838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d206093, d295838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206094 q = 1) (hb : d295839 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206094, d295839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206094, d295839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d206095 q = 1) (hb : d295840 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206095, d295840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206095, d295840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d153186 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d153190 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d290543 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d206036 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d206099 q = 1) (hb : d295842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206099, d295842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d206099, d295842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d153198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d206100 q = 1) (hb : d295843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206100, d295843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d206100, d295843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d206101 q = 1) (hb : d295844 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206101, d295844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d206101, d295844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d206102 q = 1) (hb : d295845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206102, d295845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d206102, d295845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d206103 q = 1) (hb : d295846 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d206103, d295846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d206103, d295846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75980 (p : Pattern) (ha : d207474 p = 1) (hb : d295853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d290543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d206036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206099 q = 1) (hb : d295842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d206099, d295842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206099, d295842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d153198 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d206100 q = 1) (hb : d295843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d206100, d295843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d206100, d295843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d206101 q = 1) (hb : d295851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d206101, d295851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206101, d295851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d206102 q = 1) (hb : d295852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d206102, d295852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d206102, d295852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207474 q = 1) (hb : d295853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207474, d295853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207474, d295853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75981 (p : Pattern) (ha : d207484 p = 1) (hb : d295863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d290584 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d206074 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d207480 q = 1) (hb : d295859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d207480, d295859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d207480, d295859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d153268 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207481 q = 1) (hb : d295860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d207481, d295860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207481, d295860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207482 q = 1) (hb : d295861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d207482, d295861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207482, d295861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207483 q = 1) (hb : d295862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d207483, d295862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207483, d295862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d207484 q = 1) (hb : d295863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d207484, d295863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207484, d295863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75982 (p : Pattern) (ha : d207490 p = 1) (hb : d295869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d153109 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d206104 q = 1) (hb : d295847 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d206104, d295847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75978 q ha hb
    | true =>
      simp only [d206104, d295847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75979 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153205 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d206105 q = 1) (hb : d295848 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d206105, d295848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d206105, d295848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d207472 q = 1) (hb : d295849 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207472, d295849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d207472, d295849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207473 q = 1) (hb : d295850 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207473, d295850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207473, d295850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d207475 q = 1) (hb : d295854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207475, d295854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207475, d295854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75980 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d153214 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d207476 q = 1) (hb : d295855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207476, d295855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d207476, d295855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d207477 q = 1) (hb : d295856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207477, d295856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d207477, d295856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d207478 q = 1) (hb : d295857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207478, d295857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d207478, d295857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d207479 q = 1) (hb : d295858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207479, d295858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d207479, d295858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d207485 q = 1) (hb : d295864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d207485, d295864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d207485, d295864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75981 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d153279 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d207486 q = 1) (hb : d295865 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d207486, d295865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d207486, d295865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d207487 q = 1) (hb : d295866 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d207487, d295866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d207487, d295866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d207488 q = 1) (hb : d295867 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d207488, d295867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d207488, d295867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d207489 q = 1) (hb : d295868 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d207489, d295868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d207489, d295868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d207490 q = 1) (hb : d295869 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d207490, d295869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d207490, d295869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75983 (p : Pattern) (ha : d207496 p = 1) (hb : d295875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d207491 q = 1) (hb : d295870 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d207491, d295870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207491, d295870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75982 q ha hb
  have h2 (q : Pattern) (ha : d207492 q = 1) (hb : d295871 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d207492, d295871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207492, d295871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d207493 q = 1) (hb : d295872 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d207493, d295872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207493, d295872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d207494 q = 1) (hb : d295873 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d207494, d295873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207494, d295873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d207495 q = 1) (hb : d295874 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d207495, d295874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207495, d295874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d207496 q = 1) (hb : d295875 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d207496, d295875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d207496, d295875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75984 (p : Pattern) (ha : d293465 p = 1) (hb : d295881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d290657 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290666 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d290698 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d293460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293461 q = 1) (hb : d295877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293461, d295877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293461, d295877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d290747 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d293462 q = 1) (hb : d295878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293462, d295878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293462, d295878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293463 q = 1) (hb : d295879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293463, d295879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293463, d295879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293464 q = 1) (hb : d295880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293464, d295880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293464, d295880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293465 q = 1) (hb : d295881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293465, d295881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293465, d295881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75985 (p : Pattern) (ha : d293474 p = 1) (hb : d295886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d290657 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d290666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290698 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d293460 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d293461 q = 1) (hb : d295877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293461, d295877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293461, d295877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d290747 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d293462 q = 1) (hb : d295878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293462, d295878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293462, d295878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293463 q = 1) (hb : d295879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293463, d295879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293463, d295879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293464 q = 1) (hb : d295880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293464, d295880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293464, d295880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d290757 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d290762 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d290764 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d293469 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d293470 q = 1) (hb : d295882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293470, d295882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293470, d295882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d290771 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d293471 q = 1) (hb : d295883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293471, d295883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293471, d295883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293472 q = 1) (hb : d295884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293472, d295884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293472, d295884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d293473 q = 1) (hb : d295885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293473, d295885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293473, d295885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d293474 q = 1) (hb : d295886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293474, d295886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293474, d295886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75986 (p : Pattern) (ha : d295517 p = 1) (hb : d295893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d290764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293469 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293470 q = 1) (hb : d295882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293470, d295882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293470, d295882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d290771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293471 q = 1) (hb : d295883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293471, d295883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293471, d295883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293472 q = 1) (hb : d295891 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293472, d295891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293472, d295891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293473 q = 1) (hb : d295892 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293473, d295892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293473, d295892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d295517 q = 1) (hb : d295893 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d295517, d295893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295517, d295893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75987 (p : Pattern) (ha : d295528 p = 1) (hb : d295903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d290854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d295523 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d295524 q = 1) (hb : d295899 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d295524, d295899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d295524, d295899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d290899 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d295525 q = 1) (hb : d295900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d295525, d295900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d295525, d295900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d295526 q = 1) (hb : d295901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d295526, d295901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295526, d295901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d295527 q = 1) (hb : d295902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d295527, d295902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295527, d295902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d295528 q = 1) (hb : d295903 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d295528, d295903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295528, d295903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75988 (p : Pattern) (ha : d295534 p = 1) (hb : d295909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d290649 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293475 q = 1) (hb : d295887 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293475, d295887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75984 q ha hb
    | true =>
      simp only [d293475, d295887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75985 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d290789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293476 q = 1) (hb : d295888 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293476, d295888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293476, d295888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d295515 q = 1) (hb : d295889 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d295515, d295889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d295515, d295889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d295516 q = 1) (hb : d295890 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d295516, d295890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295516, d295890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d295518 q = 1) (hb : d295894 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d295518, d295894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d295518, d295894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75986 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d290798 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d295519 q = 1) (hb : d295895 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d295519, d295895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d295519, d295895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d295520 q = 1) (hb : d295896 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d295520, d295896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d295520, d295896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d295521 q = 1) (hb : d295897 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d295521, d295897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d295521, d295897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d295522 q = 1) (hb : d295898 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d295522, d295898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d295522, d295898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d295529 q = 1) (hb : d295904 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d295529, d295904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d295529, d295904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75987 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d290915 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d295530 q = 1) (hb : d295905 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d295530, d295905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d295530, d295905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d295531 q = 1) (hb : d295906 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d295531, d295906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d295531, d295906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d295532 q = 1) (hb : d295907 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d295532, d295907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d295532, d295907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d295533 q = 1) (hb : d295908 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d295533, d295908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d295533, d295908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d295534 q = 1) (hb : d295909 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d295534, d295909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d295534, d295909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75989 (p : Pattern) (ha : d295540 p = 1) (hb : d295915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d295535 q = 1) (hb : d295910 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d295535, d295910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295535, d295910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75988 q ha hb
  have h2 (q : Pattern) (ha : d295536 q = 1) (hb : d295911 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d295536, d295911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295536, d295911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d295537 q = 1) (hb : d295912 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d295537, d295912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295537, d295912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d295538 q = 1) (hb : d295913 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d295538, d295913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295538, d295913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d295539 q = 1) (hb : d295914 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d295539, d295914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295539, d295914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d295540 q = 1) (hb : d295915 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d295540, d295915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295540, d295915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75990 (p : Pattern) (ha : d293662 p = 1) (hb : d295922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d291010 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d291019 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d291051 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d293657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293658 q = 1) (hb : d295918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293658, d295918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293658, d295918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d291114 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d293659 q = 1) (hb : d295919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293659, d295919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293659, d295919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293660 q = 1) (hb : d295920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293660, d295920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293660, d295920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293661 q = 1) (hb : d295921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293661, d295921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293661, d295921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293662 q = 1) (hb : d295922 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293662, d295922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293662, d295922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75991 (p : Pattern) (ha : d293672 p = 1) (hb : d295927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d291010 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d291019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d291051 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d293657 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d293658 q = 1) (hb : d295918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293658, d295918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293658, d295918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d291114 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d293659 q = 1) (hb : d295919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293659, d295919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293659, d295919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293660 q = 1) (hb : d295920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293660, d295920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293660, d295920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293661 q = 1) (hb : d295921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293661, d295921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293661, d295921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d291124 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d291129 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d291131 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d293667 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d293668 q = 1) (hb : d295923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293668, d295923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293668, d295923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d291138 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d293669 q = 1) (hb : d295924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293669, d295924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293669, d295924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293670 q = 1) (hb : d295925 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293670, d295925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293670, d295925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d293671 q = 1) (hb : d295926 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293671, d295926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293671, d295926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d293672 q = 1) (hb : d295927 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293672, d295927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293672, d295927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75992 (p : Pattern) (ha : d295545 p = 1) (hb : d295934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d291131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293667 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293668 q = 1) (hb : d295923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293668, d295923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293668, d295923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d291138 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293669 q = 1) (hb : d295924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293669, d295924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293669, d295924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293670 q = 1) (hb : d295932 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293670, d295932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293670, d295932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293671 q = 1) (hb : d295933 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293671, d295933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293671, d295933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d295545 q = 1) (hb : d295934 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d295545, d295934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295545, d295934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75993 (p : Pattern) (ha : d295556 p = 1) (hb : d295944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d291240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d295551 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d295552 q = 1) (hb : d295940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d295552, d295940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d295552, d295940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d291295 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d295553 q = 1) (hb : d295941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d295553, d295941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d295553, d295941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d295554 q = 1) (hb : d295942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d295554, d295942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295554, d295942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d295555 q = 1) (hb : d295943 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d295555, d295943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295555, d295943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d295556 q = 1) (hb : d295944 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d295556, d295944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295556, d295944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75994 (p : Pattern) (ha : d295562 p = 1) (hb : d295950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d291002 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d293673 q = 1) (hb : d295928 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d293673, d295928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75990 q ha hb
    | true =>
      simp only [d293673, d295928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75991 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d291156 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293674 q = 1) (hb : d295929 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293674, d295929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293674, d295929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d295543 q = 1) (hb : d295930 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d295543, d295930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d295543, d295930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d295544 q = 1) (hb : d295931 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d295544, d295931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295544, d295931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d295546 q = 1) (hb : d295935 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d295546, d295935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d295546, d295935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75992 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d291165 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d295547 q = 1) (hb : d295936 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d295547, d295936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d295547, d295936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d295548 q = 1) (hb : d295937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d295548, d295937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d295548, d295937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d295549 q = 1) (hb : d295938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d295549, d295938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d295549, d295938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d295550 q = 1) (hb : d295939 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d295550, d295939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d295550, d295939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d295557 q = 1) (hb : d295945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d295557, d295945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d295557, d295945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75993 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d291311 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d295558 q = 1) (hb : d295946 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d295558, d295946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d295558, d295946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d295559 q = 1) (hb : d295947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d295559, d295947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d295559, d295947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d295560 q = 1) (hb : d295948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d295560, d295948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d295560, d295948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d295561 q = 1) (hb : d295949 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d295561, d295949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d295561, d295949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d295562 q = 1) (hb : d295950 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d295562, d295950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d295562, d295950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro75995 (p : Pattern) (ha : d295568 p = 1) (hb : d295956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d295563 q = 1) (hb : d295951 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d295563, d295951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295563, d295951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro75994 q ha hb
  have h2 (q : Pattern) (ha : d295564 q = 1) (hb : d295952 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d295564, d295952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295564, d295952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d295565 q = 1) (hb : d295953 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d295565, d295953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295565, d295953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d295566 q = 1) (hb : d295954 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d295566, d295954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295566, d295954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d295567 q = 1) (hb : d295955 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d295567, d295955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295567, d295955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d295568 q = 1) (hb : d295956 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d295568, d295956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295568, d295956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro75996 (p : Pattern) (ha : d293954 p = 1) (hb : d295964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d291407 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d291416 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d291441 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d293949 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293950 q = 1) (hb : d295960 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293950, d295960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293950, d295960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d291521 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d293951 q = 1) (hb : d295961 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293951, d295961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d293951, d295961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293952 q = 1) (hb : d295962 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293952, d295962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293952, d295962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d293953 q = 1) (hb : d295963 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293953, d295963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293953, d295963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d293954 q = 1) (hb : d295964 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293954, d295964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293954, d295964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro75997 (p : Pattern) (ha : d293964 p = 1) (hb : d295969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d291407 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d291416 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d291441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d293949 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d293950 q = 1) (hb : d295960 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293950, d295960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d293950, d295960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d291521 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d293951 q = 1) (hb : d295961 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293951, d295961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293951, d295961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293952 q = 1) (hb : d295962 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293952, d295962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293952, d295962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d293953 q = 1) (hb : d295963 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293953, d295963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293953, d295963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d291531 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d291536 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d291538 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d293959 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d293960 q = 1) (hb : d295965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293960, d295965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d293960, d295965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d291545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d293961 q = 1) (hb : d295966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293961, d295966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d293961, d295966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d293962 q = 1) (hb : d295967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293962, d295967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d293962, d295967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d293963 q = 1) (hb : d295968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293963, d295968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d293963, d295968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d293964 q = 1) (hb : d295969 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d293964, d295969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d293964, d295969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro75998 (p : Pattern) (ha : d295574 p = 1) (hb : d295976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d291538 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d293959 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d293960 q = 1) (hb : d295965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d293960, d295965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293960, d295965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d291545 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d293961 q = 1) (hb : d295966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d293961, d295966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293961, d295966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d293962 q = 1) (hb : d295974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d293962, d295974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293962, d295974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d293963 q = 1) (hb : d295975 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d293963, d295975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d293963, d295975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d295574 q = 1) (hb : d295976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d295574, d295976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295574, d295976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro75999 (p : Pattern) (ha : d295585 p = 1) (hb : d295986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d291642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d295580 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d295581 q = 1) (hb : d295982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d295581, d295982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d295581, d295982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d291712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d295582 q = 1) (hb : d295983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d295582, d295983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d295582, d295983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d295583 q = 1) (hb : d295984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d295583, d295984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295583, d295984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d295584 q = 1) (hb : d295985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d295584, d295985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295584, d295985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d295585 q = 1) (hb : d295986 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d295585, d295986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295585, d295986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
