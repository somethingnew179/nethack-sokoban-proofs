import NetHack.Soko22Hazard87.AndIntroBlocks0010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro2750 (p : Pattern) (ha : d56021 p = 1) (hb : d64662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56016 q = 1) (hb : d64657 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d56016, d64657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2749 q ha hb
    | true =>
      simp only [d56016, d64657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d56017 q = 1) (hb : d64658 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d56017, d64658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56017, d64658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d56018 q = 1) (hb : d64659 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d56018, d64659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56018, d64659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d56019 q = 1) (hb : d64660 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d56019, d64660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56019, d64660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d56020 q = 1) (hb : d64661 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d56020, d64661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56020, d64661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d56021 q = 1) (hb : d64662 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d56021, d64662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56021, d64662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2751 (p : Pattern) (ha : d0 p = 1) (hb : d55892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55892 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2752 (p : Pattern) (ha : d0 p = 1) (hb : d56021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56021 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2753 (p : Pattern) (ha : d0 p = 1) (hb : d56141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56141 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2754 (p : Pattern) (ha : d2898 p = 1) (hb : d64663 p = 1) : d64668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d106 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d113 q = 1) : d113 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d114 q = 1) (hb : d55890 q = 1) : d64665 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d55890, d64665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114, d55890, d64665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2896 q = 1) (hb : d64663 q = 1) : d64666 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2896, d64663, d64666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2896, d64663, d64666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2526 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2527 q = 1) (hb : d55890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2527, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2528 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2528, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2528, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2897 q = 1) (hb : d64663 q = 1) : d64667 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2897, d64667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2897, d64667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2898 q = 1) (hb : d64663 q = 1) : d64668 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2898, d64668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2898, d64668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2755 (p : Pattern) (ha : d2906 p = 1) (hb : d64663 p = 1) : d64677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d286 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d293 q = 1) : d293 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d294 q = 1) (hb : d55890 q = 1) : d64674 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d55890, d64674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d294, d55890, d64674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2904 q = 1) (hb : d64663 q = 1) : d64675 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2904, d64663, d64675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2904, d64663, d64675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2538 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2539 q = 1) (hb : d55890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2539, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2540 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2540, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2540, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2905 q = 1) (hb : d64663 q = 1) : d64676 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2905, d64676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2905, d64676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2906 q = 1) (hb : d64663 q = 1) : d64677 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2906, d64677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2906, d64677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2756 (p : Pattern) (ha : d2912 p = 1) (hb : d64663 p = 1) : d64683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2899 q = 1) (hb : d64663 q = 1) : d64669 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2899, d64669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2899, d64669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2754 q ha hb
  have h2 (q : Pattern) (ha : d2900 q = 1) (hb : d64663 q = 1) : d64670 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2900, d64670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2900, d64670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2901 q = 1) (hb : d64663 q = 1) : d64671 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2901, d64671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2901, d64671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2902 q = 1) (hb : d64663 q = 1) : d64672 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2902, d64672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2902, d64672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2903 q = 1) (hb : d64663 q = 1) : d64673 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2903, d64673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2903, d64673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2907 q = 1) (hb : d64663 q = 1) : d64678 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2907, d64678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2907, d64678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2755 q ha hb
  have h7 (q : Pattern) (ha : d2908 q = 1) (hb : d64663 q = 1) : d64679 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2908, d64679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2908, d64679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2909 q = 1) (hb : d64663 q = 1) : d64680 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2909, d64680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2909, d64680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2910 q = 1) (hb : d64663 q = 1) : d64681 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2910, d64681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2910, d64681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2911 q = 1) (hb : d64663 q = 1) : d64682 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2911, d64682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2911, d64682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2912 q = 1) (hb : d64663 q = 1) : d64683 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2912, d64683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2912, d64683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2757 (p : Pattern) (ha : d2915 p = 1) (hb : d64663 p = 1) : d64687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d509 q = 1) : d509 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d510 q = 1) (hb : d55890 q = 1) : d64684 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d55890, d64684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d510, d55890, d64684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2913 q = 1) (hb : d64663 q = 1) : d64685 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2913, d64663, d64685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2913, d64663, d64685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2551 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2552 q = 1) (hb : d55890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2552, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2553 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2553, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2553, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2914 q = 1) (hb : d64663 q = 1) : d64686 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2914, d64686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2914, d64686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2915 q = 1) (hb : d64663 q = 1) : d64687 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2915, d64687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2915, d64687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2758 (p : Pattern) (ha : d2921 p = 1) (hb : d64663 p = 1) : d64693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2916 q = 1) (hb : d64663 q = 1) : d64688 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2916, d64688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2916, d64688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2757 q ha hb
  have h2 (q : Pattern) (ha : d2917 q = 1) (hb : d64663 q = 1) : d64689 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2917, d64689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2917, d64689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2918 q = 1) (hb : d64663 q = 1) : d64690 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2918, d64690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2918, d64690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2919 q = 1) (hb : d64663 q = 1) : d64691 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2919, d64691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2919, d64691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2920 q = 1) (hb : d64663 q = 1) : d64692 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2920, d64692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2920, d64692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2921 q = 1) (hb : d64663 q = 1) : d64693 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2921, d64693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2921, d64693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2759 (p : Pattern) (ha : d2925 p = 1) (hb : d64663 p = 1) : d64698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d791 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d801 q = 1) : d801 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d802 q = 1) (hb : d55890 q = 1) : d64695 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d55890, d64695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d802, d55890, d64695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2923 q = 1) (hb : d64663 q = 1) : d64696 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2923, d64663, d64696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2923, d64663, d64696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2565 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2566 q = 1) (hb : d55890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2566, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2567 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2567, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2567, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2924 q = 1) (hb : d64663 q = 1) : d64697 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2924, d64697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2924, d64697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2925 q = 1) (hb : d64663 q = 1) : d64698 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2925, d64698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2925, d64698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2760 (p : Pattern) (ha : d2931 p = 1) (hb : d64663 p = 1) : d64704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2926 q = 1) (hb : d64663 q = 1) : d64699 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2926, d64699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2926, d64699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2759 q ha hb
  have h2 (q : Pattern) (ha : d2927 q = 1) (hb : d64663 q = 1) : d64700 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2927, d64700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2927, d64700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2928 q = 1) (hb : d64663 q = 1) : d64701 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2928, d64701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2928, d64701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2929 q = 1) (hb : d64663 q = 1) : d64702 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2929, d64702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2929, d64702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2930 q = 1) (hb : d64663 q = 1) : d64703 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2930, d64703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2930, d64703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2931 q = 1) (hb : d64663 q = 1) : d64704 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2931, d64704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2931, d64704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2761 (p : Pattern) (ha : d2936 p = 1) (hb : d64663 p = 1) : d64710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1170 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1180 q = 1) : d1180 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d1181 q = 1) (hb : d55890 q = 1) : d64707 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d55890, d64707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1181, d55890, d64707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2934 q = 1) (hb : d64663 q = 1) : d64708 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2934, d64663, d64708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2934, d64663, d64708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2580 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2581 q = 1) (hb : d55890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2581, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2582 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2582, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2582, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2935 q = 1) (hb : d64663 q = 1) : d64709 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2935, d64709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2935, d64709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2936 q = 1) (hb : d64663 q = 1) : d64710 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2936, d64710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2936, d64710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2762 (p : Pattern) (ha : d2942 p = 1) (hb : d64663 p = 1) : d64716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2937 q = 1) (hb : d64663 q = 1) : d64711 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2937, d64711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2937, d64711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2761 q ha hb
  have h2 (q : Pattern) (ha : d2938 q = 1) (hb : d64663 q = 1) : d64712 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2938, d64712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2938, d64712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2939 q = 1) (hb : d64663 q = 1) : d64713 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2939, d64713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2939, d64713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2940 q = 1) (hb : d64663 q = 1) : d64714 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2940, d64714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2940, d64714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2941 q = 1) (hb : d64663 q = 1) : d64715 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2941, d64715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2941, d64715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2942 q = 1) (hb : d64663 q = 1) : d64716 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2942, d64716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2942, d64716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2763 (p : Pattern) (ha : d2948 p = 1) (hb : d64663 p = 1) : d64723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1631 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1641 q = 1) : d1641 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d1642 q = 1) (hb : d55890 q = 1) : d64720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d55890, d64720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1642, d55890, d64720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2946 q = 1) (hb : d64663 q = 1) : d64721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2946, d64663, d64721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2946, d64663, d64721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2596 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2597 q = 1) (hb : d55890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2597, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2598 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2598, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2598, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2947 q = 1) (hb : d64663 q = 1) : d64722 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2947, d64722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2947, d64722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2948 q = 1) (hb : d64663 q = 1) : d64723 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2948, d64723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2948, d64723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2764 (p : Pattern) (ha : d2954 p = 1) (hb : d64663 p = 1) : d64729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2949 q = 1) (hb : d64663 q = 1) : d64724 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2949, d64724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2949, d64724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2763 q ha hb
  have h2 (q : Pattern) (ha : d2950 q = 1) (hb : d64663 q = 1) : d64725 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2950, d64725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2950, d64725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2951 q = 1) (hb : d64663 q = 1) : d64726 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2951, d64726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2951, d64726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2952 q = 1) (hb : d64663 q = 1) : d64727 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2952, d64727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2952, d64727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2953 q = 1) (hb : d64663 q = 1) : d64728 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2953, d64728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2953, d64728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2954 q = 1) (hb : d64663 q = 1) : d64729 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2954, d64729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2954, d64729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2765 (p : Pattern) (ha : d2961 p = 1) (hb : d64663 p = 1) : d64737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2124 q = 1) : d2124 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d2125 q = 1) (hb : d55890 q = 1) : d64734 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d55890, d64734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2125, d55890, d64734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2959 q = 1) (hb : d64663 q = 1) : d64735 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2959, d64663, d64735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2959, d64663, d64735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2613 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2614 q = 1) (hb : d55890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2614, d55890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2615 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2615, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2615, d64663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2960 q = 1) (hb : d64663 q = 1) : d64736 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2960, d64736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2960, d64736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2961 q = 1) (hb : d64663 q = 1) : d64737 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2961, d64737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2961, d64737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2766 (p : Pattern) (ha : d2967 p = 1) (hb : d64663 p = 1) : d64743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2962 q = 1) (hb : d64663 q = 1) : d64738 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2962, d64738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2962, d64738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2765 q ha hb
  have h2 (q : Pattern) (ha : d2963 q = 1) (hb : d64663 q = 1) : d64739 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2963, d64739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2963, d64739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2964 q = 1) (hb : d64663 q = 1) : d64740 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2964, d64740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2964, d64740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2965 q = 1) (hb : d64663 q = 1) : d64741 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2965, d64741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2965, d64741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2966 q = 1) (hb : d64663 q = 1) : d64742 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2966, d64742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2966, d64742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2967 q = 1) (hb : d64663 q = 1) : d64743 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2967, d64743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2967, d64743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2767 (p : Pattern) (ha : d2973 p = 1) (hb : d64663 p = 1) : d64749 p = 1 := by
  have h0 (q : Pattern) (ha : d2922 q = 1) (hb : d64663 q = 1) : d64694 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2922, d64694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2756 q ha hb
    | true =>
      simp only [d2922, d64694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2758 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2932 q = 1) (hb : d64663 q = 1) : d64705 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2932, d64705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2932, d64705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2760 q ha hb
  have h3 (q : Pattern) (ha : d2933 q = 1) (hb : d64663 q = 1) : d64706 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2933, d64706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2933, d64706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2943 q = 1) (hb : d64663 q = 1) : d64717 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2943, d64717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2943, d64717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2762 q ha hb
  have h5 (q : Pattern) (ha : d2944 q = 1) (hb : d64663 q = 1) : d64718 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2944, d64718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2944, d64718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2945 q = 1) (hb : d64663 q = 1) : d64719 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2945, d64719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2945, d64719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2955 q = 1) (hb : d64663 q = 1) : d64730 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2955, d64730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2955, d64730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2764 q ha hb
  have h8 (q : Pattern) (ha : d2956 q = 1) (hb : d64663 q = 1) : d64731 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2956, d64731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2956, d64731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2957 q = 1) (hb : d64663 q = 1) : d64732 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2957, d64732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2957, d64732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2958 q = 1) (hb : d64663 q = 1) : d64733 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2958, d64733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2958, d64733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2968 q = 1) (hb : d64663 q = 1) : d64744 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2968, d64744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2968, d64744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2766 q ha hb
  have h12 (q : Pattern) (ha : d2969 q = 1) (hb : d64663 q = 1) : d64745 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2969, d64745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2969, d64745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2970 q = 1) (hb : d64663 q = 1) : d64746 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2970, d64746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2970, d64746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2971 q = 1) (hb : d64663 q = 1) : d64747 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2971, d64747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2971, d64747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2972 q = 1) (hb : d64663 q = 1) : d64748 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d2972, d64748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2972, d64748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2973 q = 1) (hb : d64663 q = 1) : d64749 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d2973, d64749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2973, d64749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2768 (p : Pattern) (ha : d2979 p = 1) (hb : d64663 p = 1) : d64755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2974 q = 1) (hb : d64663 q = 1) : d64750 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d2974, d64750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2767 q ha hb
    | true =>
      simp only [d2974, d64750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2975 q = 1) (hb : d64663 q = 1) : d64751 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d2975, d64751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2975, d64751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2976 q = 1) (hb : d64663 q = 1) : d64752 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d2976, d64752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2976, d64752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2977 q = 1) (hb : d64663 q = 1) : d64753 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d2977, d64753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2977, d64753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2978 q = 1) (hb : d64663 q = 1) : d64754 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d2978, d64754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2978, d64754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2979 q = 1) (hb : d64663 q = 1) : d64755 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d2979, d64755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2979, d64755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2769 (p : Pattern) (ha : d2985 p = 1) (hb : d64663 p = 1) : d64761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2980 q = 1) (hb : d64663 q = 1) : d64756 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d2980, d64756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2768 q ha hb
    | true =>
      simp only [d2980, d64756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2981 q = 1) (hb : d64663 q = 1) : d64757 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d2981, d64757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2981, d64757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2982 q = 1) (hb : d64663 q = 1) : d64758 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d2982, d64758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2982, d64758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2983 q = 1) (hb : d64663 q = 1) : d64759 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d2983, d64759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2983, d64759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2984 q = 1) (hb : d64663 q = 1) : d64760 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d2984, d64760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2984, d64760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2985 q = 1) (hb : d64663 q = 1) : d64761 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d2985, d64761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2985, d64761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2770 (p : Pattern) (ha : d2991 p = 1) (hb : d64663 p = 1) : d64767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2986 q = 1) (hb : d64663 q = 1) : d64762 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d2986, d64762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2769 q ha hb
    | true =>
      simp only [d2986, d64762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2987 q = 1) (hb : d64663 q = 1) : d64763 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d2987, d64763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2987, d64763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2988 q = 1) (hb : d64663 q = 1) : d64764 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d2988, d64764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2988, d64764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2989 q = 1) (hb : d64663 q = 1) : d64765 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d2989, d64765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2989, d64765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2990 q = 1) (hb : d64663 q = 1) : d64766 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d2990, d64766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2990, d64766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2991 q = 1) (hb : d64663 q = 1) : d64767 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d2991, d64767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2991, d64767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2771 (p : Pattern) (ha : d2997 p = 1) (hb : d64663 p = 1) : d64773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2992 q = 1) (hb : d64663 q = 1) : d64768 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d2992, d64768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2770 q ha hb
    | true =>
      simp only [d2992, d64768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2993 q = 1) (hb : d64663 q = 1) : d64769 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d2993, d64769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2993, d64769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2994 q = 1) (hb : d64663 q = 1) : d64770 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d2994, d64770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2994, d64770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2995 q = 1) (hb : d64663 q = 1) : d64771 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d2995, d64771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2995, d64771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2996 q = 1) (hb : d64663 q = 1) : d64772 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d2996, d64772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2996, d64772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2997 q = 1) (hb : d64663 q = 1) : d64773 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d2997, d64773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2997, d64773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2772 (p : Pattern) (ha : d3003 p = 1) (hb : d64663 p = 1) : d64779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2998 q = 1) (hb : d64663 q = 1) : d64774 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d2998, d64774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2771 q ha hb
    | true =>
      simp only [d2998, d64774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2999 q = 1) (hb : d64663 q = 1) : d64775 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d2999, d64775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2999, d64775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3000 q = 1) (hb : d64663 q = 1) : d64776 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3000, d64776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3000, d64776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3001 q = 1) (hb : d64663 q = 1) : d64777 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3001, d64777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3001, d64777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3002 q = 1) (hb : d64663 q = 1) : d64778 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3002, d64778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3002, d64778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3003 q = 1) (hb : d64663 q = 1) : d64779 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3003, d64779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3003, d64779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2773 (p : Pattern) (ha : d3009 p = 1) (hb : d64664 p = 1) : d64785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64663 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3004 q = 1) (hb : d64663 q = 1) : d64780 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3004, d64780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2772 q ha hb
    | true =>
      simp only [d3004, d64780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3005 q = 1) (hb : d64663 q = 1) : d64781 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3005, d64781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3005, d64781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3006 q = 1) (hb : d64663 q = 1) : d64782 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3006, d64782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3006, d64782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3007 q = 1) (hb : d64664 q = 1) : d64783 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3007, d64664, d64783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3007, d64664, d64783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d64664 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3008 q = 1) (hb : d64664 q = 1) : d64784 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3008, d64784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3008, d64784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3009 q = 1) (hb : d64664 q = 1) : d64785 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3009, d64785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3009, d64785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro2774 (p : Pattern) (ha : d3015 p = 1) (hb : d64664 p = 1) : d64791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64664 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3010 q = 1) (hb : d64664 q = 1) : d64786 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3010, d64786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2773 q ha hb
    | true =>
      simp only [d3010, d64786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3011 q = 1) (hb : d64664 q = 1) : d64787 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3011, d64787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3011, d64787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3012 q = 1) (hb : d64664 q = 1) : d64788 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3012, d64788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3012, d64788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3013 q = 1) (hb : d64664 q = 1) : d64789 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3013, d64789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3013, d64789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3014 q = 1) (hb : d64664 q = 1) : d64790 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3014, d64790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3014, d64790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3015 q = 1) (hb : d64664 q = 1) : d64791 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3015, d64791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3015, d64791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2775 (p : Pattern) (ha : d1 p = 1) (hb : d64791 p = 1) : d64791 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d64791 q = 1) : d64791 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro2776 (p : Pattern) (ha : d0 p = 1) (hb : d64664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64664 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2777 (p : Pattern) (ha : d2898 p = 1) (hb : d55755 p = 1) : d64075 p = 1 := by
  have h0 (q : Pattern) (ha : d2896 q = 1) (hb : d55754 q = 1) : d2896 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2897 q = 1) (hb : d55755 q = 1) : d64074 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2897, d55755, d64074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2897, d55755, d64074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2898 q = 1) (hb : d55755 q = 1) : d64075 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2898, d64075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2898, d64075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2778 (p : Pattern) (ha : d2906 p = 1) (hb : d55755 p = 1) : d64082 p = 1 := by
  have h0 (q : Pattern) (ha : d2904 q = 1) (hb : d55754 q = 1) : d2904 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2905 q = 1) (hb : d55755 q = 1) : d64081 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2905, d55755, d64081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2905, d55755, d64081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2906 q = 1) (hb : d55755 q = 1) : d64082 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2906, d64082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2906, d64082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2779 (p : Pattern) (ha : d2912 p = 1) (hb : d55755 p = 1) : d64088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2899 q = 1) (hb : d55755 q = 1) : d64076 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2899, d64076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2899, d64076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2777 q ha hb
  have h2 (q : Pattern) (ha : d2900 q = 1) (hb : d55755 q = 1) : d64077 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2900, d64077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2900, d64077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2901 q = 1) (hb : d55755 q = 1) : d64078 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2901, d64078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2901, d64078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2902 q = 1) (hb : d55755 q = 1) : d64079 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2902, d64079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2902, d64079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2903 q = 1) (hb : d55755 q = 1) : d64080 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2903, d64080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2903, d64080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2907 q = 1) (hb : d55755 q = 1) : d64083 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2907, d64083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2907, d64083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2778 q ha hb
  have h7 (q : Pattern) (ha : d2908 q = 1) (hb : d55755 q = 1) : d64084 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2908, d64084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2908, d64084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2909 q = 1) (hb : d55755 q = 1) : d64085 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2909, d64085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2909, d64085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2910 q = 1) (hb : d55755 q = 1) : d64086 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2910, d64086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2910, d64086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2911 q = 1) (hb : d55755 q = 1) : d64087 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2911, d64087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2911, d64087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2912 q = 1) (hb : d55755 q = 1) : d64088 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2912, d64088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2912, d64088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2780 (p : Pattern) (ha : d2915 p = 1) (hb : d55755 p = 1) : d64090 p = 1 := by
  have h0 (q : Pattern) (ha : d2913 q = 1) (hb : d55754 q = 1) : d2913 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2553 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2914 q = 1) (hb : d55755 q = 1) : d64089 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2914, d55755, d64089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2914, d55755, d64089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2915 q = 1) (hb : d55755 q = 1) : d64090 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2915, d64090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2915, d64090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2781 (p : Pattern) (ha : d2921 p = 1) (hb : d55755 p = 1) : d64096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2916 q = 1) (hb : d55755 q = 1) : d64091 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2916, d64091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2916, d64091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2780 q ha hb
  have h2 (q : Pattern) (ha : d2917 q = 1) (hb : d55755 q = 1) : d64092 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2917, d64092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2917, d64092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2918 q = 1) (hb : d55755 q = 1) : d64093 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2918, d64093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2918, d64093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2919 q = 1) (hb : d55755 q = 1) : d64094 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2919, d64094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2919, d64094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2920 q = 1) (hb : d55755 q = 1) : d64095 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2920, d64095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2920, d64095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2921 q = 1) (hb : d55755 q = 1) : d64096 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2921, d64096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2921, d64096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2782 (p : Pattern) (ha : d2925 p = 1) (hb : d55755 p = 1) : d64099 p = 1 := by
  have h0 (q : Pattern) (ha : d2923 q = 1) (hb : d55754 q = 1) : d2923 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2924 q = 1) (hb : d55755 q = 1) : d64098 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2924, d55755, d64098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2924, d55755, d64098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2925 q = 1) (hb : d55755 q = 1) : d64099 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2925, d64099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2925, d64099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2783 (p : Pattern) (ha : d2931 p = 1) (hb : d55755 p = 1) : d64105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2926 q = 1) (hb : d55755 q = 1) : d64100 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2926, d64100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2926, d64100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2782 q ha hb
  have h2 (q : Pattern) (ha : d2927 q = 1) (hb : d55755 q = 1) : d64101 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2927, d64101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2927, d64101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2928 q = 1) (hb : d55755 q = 1) : d64102 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2928, d64102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2928, d64102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2929 q = 1) (hb : d55755 q = 1) : d64103 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2929, d64103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2929, d64103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2930 q = 1) (hb : d55755 q = 1) : d64104 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2930, d64104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2930, d64104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2931 q = 1) (hb : d55755 q = 1) : d64105 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2931, d64105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2931, d64105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2784 (p : Pattern) (ha : d2936 p = 1) (hb : d55755 p = 1) : d64109 p = 1 := by
  have h0 (q : Pattern) (ha : d2934 q = 1) (hb : d55754 q = 1) : d2934 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2935 q = 1) (hb : d55755 q = 1) : d64108 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2935, d55755, d64108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2935, d55755, d64108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2936 q = 1) (hb : d55755 q = 1) : d64109 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2936, d64109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2936, d64109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2785 (p : Pattern) (ha : d2942 p = 1) (hb : d55755 p = 1) : d64115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2937 q = 1) (hb : d55755 q = 1) : d64110 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2937, d64110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2937, d64110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2784 q ha hb
  have h2 (q : Pattern) (ha : d2938 q = 1) (hb : d55755 q = 1) : d64111 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2938, d64111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2938, d64111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2939 q = 1) (hb : d55755 q = 1) : d64112 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2939, d64112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2939, d64112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2940 q = 1) (hb : d55755 q = 1) : d64113 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2940, d64113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2940, d64113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2941 q = 1) (hb : d55755 q = 1) : d64114 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2941, d64114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2941, d64114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2942 q = 1) (hb : d55755 q = 1) : d64115 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2942, d64115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2942, d64115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2786 (p : Pattern) (ha : d2948 p = 1) (hb : d55755 p = 1) : d64120 p = 1 := by
  have h0 (q : Pattern) (ha : d2946 q = 1) (hb : d55754 q = 1) : d2946 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2947 q = 1) (hb : d55755 q = 1) : d64119 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2947, d55755, d64119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2947, d55755, d64119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2948 q = 1) (hb : d55755 q = 1) : d64120 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2948, d64120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2948, d64120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2787 (p : Pattern) (ha : d2954 p = 1) (hb : d55755 p = 1) : d64126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2949 q = 1) (hb : d55755 q = 1) : d64121 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2949, d64121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2949, d64121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2786 q ha hb
  have h2 (q : Pattern) (ha : d2950 q = 1) (hb : d55755 q = 1) : d64122 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2950, d64122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2950, d64122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2951 q = 1) (hb : d55755 q = 1) : d64123 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2951, d64123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2951, d64123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2952 q = 1) (hb : d55755 q = 1) : d64124 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2952, d64124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2952, d64124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2953 q = 1) (hb : d55755 q = 1) : d64125 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2953, d64125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2953, d64125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2954 q = 1) (hb : d55755 q = 1) : d64126 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2954, d64126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2954, d64126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2788 (p : Pattern) (ha : d2961 p = 1) (hb : d55755 p = 1) : d64132 p = 1 := by
  have h0 (q : Pattern) (ha : d2959 q = 1) (hb : d55754 q = 1) : d2959 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2960 q = 1) (hb : d55755 q = 1) : d64131 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2960, d55755, d64131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2960, d55755, d64131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2961 q = 1) (hb : d55755 q = 1) : d64132 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2961, d64132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2961, d64132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2789 (p : Pattern) (ha : d2967 p = 1) (hb : d55755 p = 1) : d64138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2962 q = 1) (hb : d55755 q = 1) : d64133 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2962, d64133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2962, d64133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2788 q ha hb
  have h2 (q : Pattern) (ha : d2963 q = 1) (hb : d55755 q = 1) : d64134 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2963, d64134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2963, d64134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2964 q = 1) (hb : d55755 q = 1) : d64135 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2964, d64135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2964, d64135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2965 q = 1) (hb : d55755 q = 1) : d64136 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2965, d64136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2965, d64136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2966 q = 1) (hb : d55755 q = 1) : d64137 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2966, d64137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2966, d64137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2967 q = 1) (hb : d55755 q = 1) : d64138 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2967, d64138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2967, d64138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2790 (p : Pattern) (ha : d2973 p = 1) (hb : d55755 p = 1) : d64144 p = 1 := by
  have h0 (q : Pattern) (ha : d2922 q = 1) (hb : d55755 q = 1) : d64097 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2922, d64097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2779 q ha hb
    | true =>
      simp only [d2922, d64097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2781 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2932 q = 1) (hb : d55755 q = 1) : d64106 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2932, d64106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2932, d64106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2783 q ha hb
  have h3 (q : Pattern) (ha : d2933 q = 1) (hb : d55755 q = 1) : d64107 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2933, d64107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2933, d64107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2943 q = 1) (hb : d55755 q = 1) : d64116 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2943, d64116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2943, d64116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2785 q ha hb
  have h5 (q : Pattern) (ha : d2944 q = 1) (hb : d55755 q = 1) : d64117 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2944, d64117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2944, d64117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2945 q = 1) (hb : d55755 q = 1) : d64118 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2945, d64118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2945, d64118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2955 q = 1) (hb : d55755 q = 1) : d64127 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2955, d64127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2955, d64127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2787 q ha hb
  have h8 (q : Pattern) (ha : d2956 q = 1) (hb : d55755 q = 1) : d64128 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2956, d64128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2956, d64128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2957 q = 1) (hb : d55755 q = 1) : d64129 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2957, d64129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2957, d64129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2958 q = 1) (hb : d55755 q = 1) : d64130 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2958, d64130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2958, d64130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2968 q = 1) (hb : d55755 q = 1) : d64139 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2968, d64139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2968, d64139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2789 q ha hb
  have h12 (q : Pattern) (ha : d2969 q = 1) (hb : d55755 q = 1) : d64140 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2969, d64140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2969, d64140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2970 q = 1) (hb : d55755 q = 1) : d64141 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2970, d64141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2970, d64141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2971 q = 1) (hb : d55755 q = 1) : d64142 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2971, d64142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2971, d64142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2972 q = 1) (hb : d55755 q = 1) : d64143 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d2972, d64143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2972, d64143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2973 q = 1) (hb : d55755 q = 1) : d64144 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d2973, d64144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2973, d64144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2791 (p : Pattern) (ha : d2979 p = 1) (hb : d55755 p = 1) : d64150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2974 q = 1) (hb : d55755 q = 1) : d64145 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d2974, d64145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2790 q ha hb
    | true =>
      simp only [d2974, d64145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2975 q = 1) (hb : d55755 q = 1) : d64146 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d2975, d64146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2975, d64146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2976 q = 1) (hb : d55755 q = 1) : d64147 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d2976, d64147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2976, d64147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2977 q = 1) (hb : d55755 q = 1) : d64148 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d2977, d64148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2977, d64148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2978 q = 1) (hb : d55755 q = 1) : d64149 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d2978, d64149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2978, d64149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2979 q = 1) (hb : d55755 q = 1) : d64150 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d2979, d64150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2979, d64150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2792 (p : Pattern) (ha : d2985 p = 1) (hb : d55755 p = 1) : d64156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2980 q = 1) (hb : d55755 q = 1) : d64151 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d2980, d64151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2791 q ha hb
    | true =>
      simp only [d2980, d64151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2981 q = 1) (hb : d55755 q = 1) : d64152 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d2981, d64152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2981, d64152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2982 q = 1) (hb : d55755 q = 1) : d64153 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d2982, d64153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2982, d64153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2983 q = 1) (hb : d55755 q = 1) : d64154 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d2983, d64154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2983, d64154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2984 q = 1) (hb : d55755 q = 1) : d64155 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d2984, d64155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2984, d64155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2985 q = 1) (hb : d55755 q = 1) : d64156 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d2985, d64156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2985, d64156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2793 (p : Pattern) (ha : d2991 p = 1) (hb : d55755 p = 1) : d64162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2986 q = 1) (hb : d55755 q = 1) : d64157 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d2986, d64157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2792 q ha hb
    | true =>
      simp only [d2986, d64157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2987 q = 1) (hb : d55755 q = 1) : d64158 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d2987, d64158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2987, d64158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2988 q = 1) (hb : d55755 q = 1) : d64159 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d2988, d64159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2988, d64159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2989 q = 1) (hb : d55755 q = 1) : d64160 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d2989, d64160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2989, d64160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2990 q = 1) (hb : d55755 q = 1) : d64161 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d2990, d64161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2990, d64161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2991 q = 1) (hb : d55755 q = 1) : d64162 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d2991, d64162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2991, d64162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2794 (p : Pattern) (ha : d2997 p = 1) (hb : d55755 p = 1) : d64168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2992 q = 1) (hb : d55755 q = 1) : d64163 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d2992, d64163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2793 q ha hb
    | true =>
      simp only [d2992, d64163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2993 q = 1) (hb : d55755 q = 1) : d64164 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d2993, d64164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2993, d64164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2994 q = 1) (hb : d55755 q = 1) : d64165 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d2994, d64165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2994, d64165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2995 q = 1) (hb : d55755 q = 1) : d64166 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d2995, d64166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2995, d64166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2996 q = 1) (hb : d55755 q = 1) : d64167 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d2996, d64167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2996, d64167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2997 q = 1) (hb : d55755 q = 1) : d64168 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d2997, d64168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2997, d64168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2795 (p : Pattern) (ha : d3003 p = 1) (hb : d55755 p = 1) : d64174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2998 q = 1) (hb : d55755 q = 1) : d64169 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d2998, d64169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2794 q ha hb
    | true =>
      simp only [d2998, d64169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2999 q = 1) (hb : d55755 q = 1) : d64170 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d2999, d64170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2999, d64170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3000 q = 1) (hb : d55755 q = 1) : d64171 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3000, d64171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3000, d64171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3001 q = 1) (hb : d55755 q = 1) : d64172 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3001, d64172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3001, d64172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3002 q = 1) (hb : d55755 q = 1) : d64173 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3002, d64173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3002, d64173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3003 q = 1) (hb : d55755 q = 1) : d64174 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3003, d64174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3003, d64174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2796 (p : Pattern) (ha : d3009 p = 1) (hb : d55755 p = 1) : d64180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3004 q = 1) (hb : d55755 q = 1) : d64175 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3004, d64175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2795 q ha hb
    | true =>
      simp only [d3004, d64175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3005 q = 1) (hb : d55755 q = 1) : d64176 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3005, d64176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3005, d64176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3006 q = 1) (hb : d55755 q = 1) : d64177 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3006, d64177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3006, d64177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3007 q = 1) (hb : d55755 q = 1) : d64178 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3007, d64178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3007, d64178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3008 q = 1) (hb : d55755 q = 1) : d64179 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3008, d64179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3008, d64179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3009 q = 1) (hb : d55755 q = 1) : d64180 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3009, d64180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3009, d64180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2797 (p : Pattern) (ha : d3015 p = 1) (hb : d55755 p = 1) : d64186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3010 q = 1) (hb : d55755 q = 1) : d64181 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3010, d64181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2796 q ha hb
    | true =>
      simp only [d3010, d64181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3011 q = 1) (hb : d55755 q = 1) : d64182 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3011, d64182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3011, d64182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3012 q = 1) (hb : d55755 q = 1) : d64183 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3012, d64183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3012, d64183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3013 q = 1) (hb : d55755 q = 1) : d64184 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3013, d64184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3013, d64184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3014 q = 1) (hb : d55755 q = 1) : d64185 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3014, d64185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3014, d64185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3015 q = 1) (hb : d55755 q = 1) : d64186 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3015, d64186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3015, d64186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2798 (p : Pattern) (ha : d54639 p = 1) (hb : d64075 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2896 q = 1) (hb : d52035 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2896, d52035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2896, d52035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54638 q = 1) (hb : d64074 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54638, d64074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d54638, d64074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d54639 q = 1) (hb : d64075 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54639, d64075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54639, d64075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro2799 (p : Pattern) (ha : d54646 p = 1) (hb : d64082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2904 q = 1) (hb : d52167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2904, d52167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2904, d52167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54645 q = 1) (hb : d64081 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54645, d64081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d54645, d64081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d54646 q = 1) (hb : d64082 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54646, d64082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54646, d64082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro2800 (p : Pattern) (ha : d54652 p = 1) (hb : d64088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54640 q = 1) (hb : d64076 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54640, d64076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54640, d64076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2798 q ha hb
  have h3 (q : Pattern) (ha : d54641 q = 1) (hb : d64077 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54641, d64077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54641, d64077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54642 q = 1) (hb : d64078 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54642, d64078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54642, d64078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54643 q = 1) (hb : d64079 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54643, d64079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54643, d64079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54644 q = 1) (hb : d64080 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54644, d64080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54644, d64080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54647 q = 1) (hb : d64083 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54647, d64083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54647, d64083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2799 q ha hb
  have h8 (q : Pattern) (ha : d54648 q = 1) (hb : d64084 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54648, d64084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54648, d64084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54649 q = 1) (hb : d64085 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54649, d64085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54649, d64085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54650 q = 1) (hb : d64086 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54650, d64086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54650, d64086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54651 q = 1) (hb : d64087 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54651, d64087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54651, d64087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54652 q = 1) (hb : d64088 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54652, d64088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54652, d64088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2801 (p : Pattern) (ha : d54654 p = 1) (hb : d64090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2913 q = 1) (hb : d52352 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2913, d52352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2913, d52352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54653 q = 1) (hb : d64089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54653, d64089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d54653, d64089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d54654 q = 1) (hb : d64090 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54654, d64090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54654, d64090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro2802 (p : Pattern) (ha : d54660 p = 1) (hb : d64096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54655 q = 1) (hb : d64091 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54655, d64091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54655, d64091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2801 q ha hb
  have h2 (q : Pattern) (ha : d54656 q = 1) (hb : d64092 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54656, d64092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54656, d64092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54657 q = 1) (hb : d64093 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54657, d64093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54657, d64093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54658 q = 1) (hb : d64094 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54658, d64094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54658, d64094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54659 q = 1) (hb : d64095 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54659, d64095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54659, d64095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54660 q = 1) (hb : d64096 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54660, d64096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54660, d64096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2803 (p : Pattern) (ha : d54663 p = 1) (hb : d64099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro111 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2923 q = 1) (hb : d52573 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2923, d52573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2923, d52573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54662 q = 1) (hb : d64098 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54662, d64098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d54662, d64098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d54663 q = 1) (hb : d64099 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54663, d64099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54663, d64099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro2804 (p : Pattern) (ha : d54669 p = 1) (hb : d64105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54664 q = 1) (hb : d64100 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54664, d64100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54664, d64100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2803 q ha hb
  have h2 (q : Pattern) (ha : d54665 q = 1) (hb : d64101 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54665, d64101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54665, d64101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54666 q = 1) (hb : d64102 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54666, d64102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54666, d64102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54667 q = 1) (hb : d64103 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54667, d64103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54667, d64103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54668 q = 1) (hb : d64104 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54668, d64104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54668, d64104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54669 q = 1) (hb : d64105 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54669, d64105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54669, d64105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2805 (p : Pattern) (ha : d54673 p = 1) (hb : d64109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro163 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2934 q = 1) (hb : d52853 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2934, d52853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2934, d52853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54672 q = 1) (hb : d64108 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54672, d64108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d54672, d64108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d54673 q = 1) (hb : d64109 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54673, d64109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54673, d64109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro2806 (p : Pattern) (ha : d54679 p = 1) (hb : d64115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54674 q = 1) (hb : d64110 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54674, d64110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54674, d64110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2805 q ha hb
  have h2 (q : Pattern) (ha : d54675 q = 1) (hb : d64111 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54675, d64111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54675, d64111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54676 q = 1) (hb : d64112 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54676, d64112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54676, d64112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54677 q = 1) (hb : d64113 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54677, d64113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54677, d64113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54678 q = 1) (hb : d64114 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54678, d64114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54678, d64114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54679 q = 1) (hb : d64115 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54679, d64115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54679, d64115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2807 (p : Pattern) (ha : d54684 p = 1) (hb : d64120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro221 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2946 q = 1) (hb : d53168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2946, d53168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2946, d53168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54683 q = 1) (hb : d64119 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54683, d64119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d54683, d64119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d54684 q = 1) (hb : d64120 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54684, d64120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54684, d64120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro2808 (p : Pattern) (ha : d54690 p = 1) (hb : d64126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54685 q = 1) (hb : d64121 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54685, d64121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54685, d64121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2807 q ha hb
  have h2 (q : Pattern) (ha : d54686 q = 1) (hb : d64122 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54686, d64122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54686, d64122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54687 q = 1) (hb : d64123 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54687, d64123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54687, d64123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54688 q = 1) (hb : d64124 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54688, d64124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54688, d64124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54689 q = 1) (hb : d64125 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54689, d64125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54689, d64125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54690 q = 1) (hb : d64126 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54690, d64126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54690, d64126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2809 (p : Pattern) (ha : d54696 p = 1) (hb : d64132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro280 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2959 q = 1) (hb : d53485 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2959, d53485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2959, d53485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54695 q = 1) (hb : d64131 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54695, d64131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d54695, d64131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d54696 q = 1) (hb : d64132 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54696, d64132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54696, d64132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro2810 (p : Pattern) (ha : d54702 p = 1) (hb : d64138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54697 q = 1) (hb : d64133 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54697, d64133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54697, d64133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2809 q ha hb
  have h2 (q : Pattern) (ha : d54698 q = 1) (hb : d64134 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54698, d64134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54698, d64134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54699 q = 1) (hb : d64135 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54699, d64135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54699, d64135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54700 q = 1) (hb : d64136 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54700, d64136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54700, d64136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54701 q = 1) (hb : d64137 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54701, d64137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54701, d64137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54702 q = 1) (hb : d64138 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54702, d64138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54702, d64138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2811 (p : Pattern) (ha : d54708 p = 1) (hb : d64144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54661 q = 1) (hb : d64097 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54661, d64097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2800 q ha hb
    | true =>
      simp only [d54661, d64097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2802 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54670 q = 1) (hb : d64106 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54670, d64106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54670, d64106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2804 q ha hb
  have h3 (q : Pattern) (ha : d54671 q = 1) (hb : d64107 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54671, d64107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54671, d64107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54680 q = 1) (hb : d64116 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54680, d64116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54680, d64116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2806 q ha hb
  have h5 (q : Pattern) (ha : d54681 q = 1) (hb : d64117 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54681, d64117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54681, d64117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54682 q = 1) (hb : d64118 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54682, d64118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54682, d64118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54691 q = 1) (hb : d64127 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54691, d64127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54691, d64127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2808 q ha hb
  have h8 (q : Pattern) (ha : d54692 q = 1) (hb : d64128 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54692, d64128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54692, d64128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54693 q = 1) (hb : d64129 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54693, d64129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54693, d64129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54694 q = 1) (hb : d64130 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54694, d64130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54694, d64130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54703 q = 1) (hb : d64139 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54703, d64139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54703, d64139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2810 q ha hb
  have h12 (q : Pattern) (ha : d54704 q = 1) (hb : d64140 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54704, d64140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54704, d64140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54705 q = 1) (hb : d64141 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54705, d64141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54705, d64141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54706 q = 1) (hb : d64142 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54706, d64142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54706, d64142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54707 q = 1) (hb : d64143 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54707, d64143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54707, d64143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54708 q = 1) (hb : d64144 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54708, d64144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54708, d64144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro2812 (p : Pattern) (ha : d54714 p = 1) (hb : d64150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54709 q = 1) (hb : d64145 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54709, d64145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2811 q ha hb
    | true =>
      simp only [d54709, d64145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54710 q = 1) (hb : d64146 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54710, d64146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54710, d64146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54711 q = 1) (hb : d64147 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54711, d64147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54711, d64147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54712 q = 1) (hb : d64148 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54712, d64148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54712, d64148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54713 q = 1) (hb : d64149 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54713, d64149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54713, d64149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54714 q = 1) (hb : d64150 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54714, d64150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54714, d64150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2813 (p : Pattern) (ha : d54720 p = 1) (hb : d64156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54715 q = 1) (hb : d64151 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54715, d64151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2812 q ha hb
    | true =>
      simp only [d54715, d64151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54716 q = 1) (hb : d64152 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54716, d64152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54716, d64152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54717 q = 1) (hb : d64153 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54717, d64153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54717, d64153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54718 q = 1) (hb : d64154 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54718, d64154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54718, d64154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54719 q = 1) (hb : d64155 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54719, d64155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54719, d64155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54720 q = 1) (hb : d64156 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54720, d64156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54720, d64156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2814 (p : Pattern) (ha : d54726 p = 1) (hb : d64162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54721 q = 1) (hb : d64157 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54721, d64157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2813 q ha hb
    | true =>
      simp only [d54721, d64157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54722 q = 1) (hb : d64158 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54722, d64158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54722, d64158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54723 q = 1) (hb : d64159 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54723, d64159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54723, d64159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54724 q = 1) (hb : d64160 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54724, d64160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54724, d64160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54725 q = 1) (hb : d64161 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54725, d64161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54725, d64161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54726 q = 1) (hb : d64162 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54726, d64162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54726, d64162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2815 (p : Pattern) (ha : d54732 p = 1) (hb : d64168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54727 q = 1) (hb : d64163 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54727, d64163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2814 q ha hb
    | true =>
      simp only [d54727, d64163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54728 q = 1) (hb : d64164 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54728, d64164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54728, d64164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54729 q = 1) (hb : d64165 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54729, d64165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54729, d64165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54730 q = 1) (hb : d64166 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54730, d64166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54730, d64166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54731 q = 1) (hb : d64167 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54731, d64167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54731, d64167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54732 q = 1) (hb : d64168 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54732, d64168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54732, d64168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2816 (p : Pattern) (ha : d54738 p = 1) (hb : d64174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54733 q = 1) (hb : d64169 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54733, d64169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2815 q ha hb
    | true =>
      simp only [d54733, d64169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54734 q = 1) (hb : d64170 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54734, d64170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54734, d64170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54735 q = 1) (hb : d64171 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54735, d64171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54735, d64171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54736 q = 1) (hb : d64172 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54736, d64172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54736, d64172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54737 q = 1) (hb : d64173 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54737, d64173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54737, d64173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54738 q = 1) (hb : d64174 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54738, d64174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54738, d64174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2817 (p : Pattern) (ha : d54744 p = 1) (hb : d64180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54739 q = 1) (hb : d64175 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54739, d64175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2816 q ha hb
    | true =>
      simp only [d54739, d64175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54740 q = 1) (hb : d64176 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54740, d64176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54740, d64176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54741 q = 1) (hb : d64177 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54741, d64177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54741, d64177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54742 q = 1) (hb : d64178 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54742, d64178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54742, d64178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54743 q = 1) (hb : d64179 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54743, d64179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54743, d64179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54744 q = 1) (hb : d64180 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54744, d64180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54744, d64180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2818 (p : Pattern) (ha : d54750 p = 1) (hb : d64186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54745 q = 1) (hb : d64181 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54745, d64181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2817 q ha hb
    | true =>
      simp only [d54745, d64181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54746 q = 1) (hb : d64182 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54746, d64182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54746, d64182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54747 q = 1) (hb : d64183 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54747, d64183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54747, d64183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54748 q = 1) (hb : d64184 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54748, d64184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54748, d64184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54749 q = 1) (hb : d64185 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54749, d64185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54749, d64185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54750 q = 1) (hb : d64186 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54750, d64186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54750, d64186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2819 (p : Pattern) (ha : d0 p = 1) (hb : d55755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55755 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2820 (p : Pattern) (ha : d0 p = 1) (hb : d54750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54750 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2821 (p : Pattern) (ha : d0 p = 1) (hb : d54863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54863 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2822 (p : Pattern) (ha : d2898 p = 1) (hb : d61810 p = 1) : d55349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2896 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2528 q = 1) (hb : d55754 q = 1) : d2528 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2897 q = 1) (hb : d61809 q = 1) : d55348 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2897, d61809, d55348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2897, d61809, d55348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2898 q = 1) (hb : d61810 q = 1) : d55349 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2898, d61810, d55349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2898, d61810, d55349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2823 (p : Pattern) (ha : d2906 p = 1) (hb : d61810 p = 1) : d55356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2904 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2540 q = 1) (hb : d55754 q = 1) : d2540 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2905 q = 1) (hb : d61809 q = 1) : d55355 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2905, d61809, d55355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2905, d61809, d55355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2906 q = 1) (hb : d61810 q = 1) : d55356 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2906, d61810, d55356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2906, d61810, d55356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2824 (p : Pattern) (ha : d2912 p = 1) (hb : d61810 p = 1) : d55362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2899 q = 1) (hb : d61810 q = 1) : d55350 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2899, d55350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2899, d55350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2822 q ha hb
  have h2 (q : Pattern) (ha : d2900 q = 1) (hb : d61810 q = 1) : d55351 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2900, d55351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2900, d55351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2901 q = 1) (hb : d61810 q = 1) : d55352 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2901, d55352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2901, d55352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2902 q = 1) (hb : d61810 q = 1) : d55353 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2902, d55353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2902, d55353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2903 q = 1) (hb : d61810 q = 1) : d55354 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2903, d55354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2903, d55354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2907 q = 1) (hb : d61810 q = 1) : d55357 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2907, d55357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2907, d55357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2823 q ha hb
  have h7 (q : Pattern) (ha : d2908 q = 1) (hb : d61810 q = 1) : d55358 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2908, d55358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2908, d55358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2909 q = 1) (hb : d61810 q = 1) : d55359 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2909, d55359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2909, d55359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2910 q = 1) (hb : d61810 q = 1) : d55360 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2910, d55360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2910, d55360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2911 q = 1) (hb : d61810 q = 1) : d55361 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2911, d55361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2911, d55361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2912 q = 1) (hb : d61810 q = 1) : d55362 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2912, d55362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2912, d55362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2825 (p : Pattern) (ha : d2915 p = 1) (hb : d61810 p = 1) : d55364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2913 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2553 q = 1) (hb : d55754 q = 1) : d2553 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2914 q = 1) (hb : d61809 q = 1) : d55363 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2914, d61809, d55363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2914, d61809, d55363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2915 q = 1) (hb : d61810 q = 1) : d55364 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2915, d61810, d55364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2915, d61810, d55364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2826 (p : Pattern) (ha : d2921 p = 1) (hb : d61810 p = 1) : d55370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2916 q = 1) (hb : d61810 q = 1) : d55365 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2916, d55365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2916, d55365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2825 q ha hb
  have h2 (q : Pattern) (ha : d2917 q = 1) (hb : d61810 q = 1) : d55366 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2917, d55366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2917, d55366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2918 q = 1) (hb : d61810 q = 1) : d55367 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2918, d55367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2918, d55367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2919 q = 1) (hb : d61810 q = 1) : d55368 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2919, d55368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2919, d55368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2920 q = 1) (hb : d61810 q = 1) : d55369 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2920, d55369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2920, d55369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2921 q = 1) (hb : d61810 q = 1) : d55370 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2921, d55370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2921, d55370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2827 (p : Pattern) (ha : d2925 p = 1) (hb : d61810 p = 1) : d55373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2923 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2567 q = 1) (hb : d55754 q = 1) : d2567 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2924 q = 1) (hb : d61809 q = 1) : d55372 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2924, d61809, d55372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2924, d61809, d55372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2925 q = 1) (hb : d61810 q = 1) : d55373 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2925, d61810, d55373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2925, d61810, d55373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2828 (p : Pattern) (ha : d2931 p = 1) (hb : d61810 p = 1) : d55379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2926 q = 1) (hb : d61810 q = 1) : d55374 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2926, d55374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2926, d55374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2827 q ha hb
  have h2 (q : Pattern) (ha : d2927 q = 1) (hb : d61810 q = 1) : d55375 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2927, d55375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2927, d55375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2928 q = 1) (hb : d61810 q = 1) : d55376 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2928, d55376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2928, d55376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2929 q = 1) (hb : d61810 q = 1) : d55377 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2929, d55377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2929, d55377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2930 q = 1) (hb : d61810 q = 1) : d55378 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2930, d55378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2930, d55378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2931 q = 1) (hb : d61810 q = 1) : d55379 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2931, d55379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2931, d55379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2829 (p : Pattern) (ha : d2936 p = 1) (hb : d61810 p = 1) : d55383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2582 q = 1) (hb : d55754 q = 1) : d2582 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2935 q = 1) (hb : d61809 q = 1) : d55382 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2935, d61809, d55382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2935, d61809, d55382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2936 q = 1) (hb : d61810 q = 1) : d55383 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2936, d61810, d55383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2936, d61810, d55383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2830 (p : Pattern) (ha : d2942 p = 1) (hb : d61810 p = 1) : d55389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2937 q = 1) (hb : d61810 q = 1) : d55384 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2937, d55384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2937, d55384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2829 q ha hb
  have h2 (q : Pattern) (ha : d2938 q = 1) (hb : d61810 q = 1) : d55385 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2938, d55385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2938, d55385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2939 q = 1) (hb : d61810 q = 1) : d55386 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2939, d55386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2939, d55386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2940 q = 1) (hb : d61810 q = 1) : d55387 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2940, d55387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2940, d55387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2941 q = 1) (hb : d61810 q = 1) : d55388 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2941, d55388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2941, d55388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2942 q = 1) (hb : d61810 q = 1) : d55389 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2942, d55389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2942, d55389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2831 (p : Pattern) (ha : d2948 p = 1) (hb : d61810 p = 1) : d55394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2946 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2598 q = 1) (hb : d55754 q = 1) : d2598 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2947 q = 1) (hb : d61809 q = 1) : d55393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2947, d61809, d55393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2947, d61809, d55393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2948 q = 1) (hb : d61810 q = 1) : d55394 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2948, d61810, d55394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2948, d61810, d55394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2832 (p : Pattern) (ha : d2954 p = 1) (hb : d61810 p = 1) : d55400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2949 q = 1) (hb : d61810 q = 1) : d55395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2949, d55395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2949, d55395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2831 q ha hb
  have h2 (q : Pattern) (ha : d2950 q = 1) (hb : d61810 q = 1) : d55396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2950, d55396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2950, d55396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2951 q = 1) (hb : d61810 q = 1) : d55397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2951, d55397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2951, d55397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2952 q = 1) (hb : d61810 q = 1) : d55398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2952, d55398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2952, d55398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2953 q = 1) (hb : d61810 q = 1) : d55399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2953, d55399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2953, d55399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2954 q = 1) (hb : d61810 q = 1) : d55400 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2954, d55400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2954, d55400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2833 (p : Pattern) (ha : d2961 p = 1) (hb : d61810 p = 1) : d55406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2615 q = 1) (hb : d55754 q = 1) : d2615 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2960 q = 1) (hb : d61809 q = 1) : d55405 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2960, d61809, d55405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2960, d61809, d55405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2961 q = 1) (hb : d61810 q = 1) : d55406 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2961, d61810, d55406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2961, d61810, d55406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2834 (p : Pattern) (ha : d2967 p = 1) (hb : d61810 p = 1) : d55412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2962 q = 1) (hb : d61810 q = 1) : d55407 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2962, d55407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2962, d55407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2833 q ha hb
  have h2 (q : Pattern) (ha : d2963 q = 1) (hb : d61810 q = 1) : d55408 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2963, d55408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2963, d55408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2964 q = 1) (hb : d61810 q = 1) : d55409 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2964, d55409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2964, d55409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2965 q = 1) (hb : d61810 q = 1) : d55410 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2965, d55410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2965, d55410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2966 q = 1) (hb : d61810 q = 1) : d55411 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2966, d55411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2966, d55411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2967 q = 1) (hb : d61810 q = 1) : d55412 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2967, d55412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2967, d55412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2835 (p : Pattern) (ha : d2973 p = 1) (hb : d61810 p = 1) : d55418 p = 1 := by
  have h0 (q : Pattern) (ha : d2922 q = 1) (hb : d61810 q = 1) : d55371 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2922, d55371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2824 q ha hb
    | true =>
      simp only [d2922, d55371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2826 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2932 q = 1) (hb : d61810 q = 1) : d55380 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2932, d55380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2932, d55380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2828 q ha hb
  have h3 (q : Pattern) (ha : d2933 q = 1) (hb : d61810 q = 1) : d55381 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2933, d55381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2933, d55381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2943 q = 1) (hb : d61810 q = 1) : d55390 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2943, d55390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2943, d55390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2830 q ha hb
  have h5 (q : Pattern) (ha : d2944 q = 1) (hb : d61810 q = 1) : d55391 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2944, d55391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2944, d55391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2945 q = 1) (hb : d61810 q = 1) : d55392 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2945, d55392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2945, d55392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2955 q = 1) (hb : d61810 q = 1) : d55401 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2955, d55401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2955, d55401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2832 q ha hb
  have h8 (q : Pattern) (ha : d2956 q = 1) (hb : d61810 q = 1) : d55402 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2956, d55402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2956, d55402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2957 q = 1) (hb : d61810 q = 1) : d55403 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2957, d55403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2957, d55403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2958 q = 1) (hb : d61810 q = 1) : d55404 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2958, d55404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2958, d55404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2968 q = 1) (hb : d61810 q = 1) : d55413 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2968, d55413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2968, d55413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2834 q ha hb
  have h12 (q : Pattern) (ha : d2969 q = 1) (hb : d61810 q = 1) : d55414 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2969, d55414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2969, d55414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2970 q = 1) (hb : d61810 q = 1) : d55415 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2970, d55415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2970, d55415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2971 q = 1) (hb : d61810 q = 1) : d55416 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2971, d55416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2971, d55416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2972 q = 1) (hb : d61810 q = 1) : d55417 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d2972, d55417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2972, d55417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2973 q = 1) (hb : d61810 q = 1) : d55418 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d2973, d55418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2973, d55418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2836 (p : Pattern) (ha : d2979 p = 1) (hb : d61810 p = 1) : d55424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2974 q = 1) (hb : d61810 q = 1) : d55419 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d2974, d55419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2835 q ha hb
    | true =>
      simp only [d2974, d55419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2975 q = 1) (hb : d61810 q = 1) : d55420 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d2975, d55420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2975, d55420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2976 q = 1) (hb : d61810 q = 1) : d55421 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d2976, d55421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2976, d55421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2977 q = 1) (hb : d61810 q = 1) : d55422 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d2977, d55422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2977, d55422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2978 q = 1) (hb : d61810 q = 1) : d55423 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d2978, d55423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2978, d55423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2979 q = 1) (hb : d61810 q = 1) : d55424 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d2979, d55424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2979, d55424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2837 (p : Pattern) (ha : d2985 p = 1) (hb : d61810 p = 1) : d55430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2980 q = 1) (hb : d61810 q = 1) : d55425 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d2980, d55425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2836 q ha hb
    | true =>
      simp only [d2980, d55425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2981 q = 1) (hb : d61810 q = 1) : d55426 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d2981, d55426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2981, d55426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2982 q = 1) (hb : d61810 q = 1) : d55427 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d2982, d55427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2982, d55427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2983 q = 1) (hb : d61810 q = 1) : d55428 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d2983, d55428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2983, d55428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2984 q = 1) (hb : d61810 q = 1) : d55429 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d2984, d55429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2984, d55429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2985 q = 1) (hb : d61810 q = 1) : d55430 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d2985, d55430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2985, d55430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2838 (p : Pattern) (ha : d2991 p = 1) (hb : d61810 p = 1) : d55436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2986 q = 1) (hb : d61810 q = 1) : d55431 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d2986, d55431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2837 q ha hb
    | true =>
      simp only [d2986, d55431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2987 q = 1) (hb : d61810 q = 1) : d55432 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d2987, d55432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2987, d55432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2988 q = 1) (hb : d61810 q = 1) : d55433 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d2988, d55433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2988, d55433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2989 q = 1) (hb : d61810 q = 1) : d55434 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d2989, d55434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2989, d55434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2990 q = 1) (hb : d61810 q = 1) : d55435 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d2990, d55435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2990, d55435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2991 q = 1) (hb : d61810 q = 1) : d55436 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d2991, d55436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2991, d55436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2839 (p : Pattern) (ha : d2997 p = 1) (hb : d61810 p = 1) : d55442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2992 q = 1) (hb : d61810 q = 1) : d55437 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d2992, d55437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2838 q ha hb
    | true =>
      simp only [d2992, d55437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2993 q = 1) (hb : d61810 q = 1) : d55438 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d2993, d55438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2993, d55438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2994 q = 1) (hb : d61810 q = 1) : d55439 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d2994, d55439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2994, d55439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2995 q = 1) (hb : d61810 q = 1) : d55440 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d2995, d55440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2995, d55440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2996 q = 1) (hb : d61810 q = 1) : d55441 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d2996, d55441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2996, d55441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2997 q = 1) (hb : d61810 q = 1) : d55442 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d2997, d55442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2997, d55442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2840 (p : Pattern) (ha : d3003 p = 1) (hb : d61810 p = 1) : d55448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2998 q = 1) (hb : d61810 q = 1) : d55443 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d2998, d55443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2839 q ha hb
    | true =>
      simp only [d2998, d55443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2999 q = 1) (hb : d61810 q = 1) : d55444 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d2999, d55444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2999, d55444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3000 q = 1) (hb : d61810 q = 1) : d55445 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3000, d55445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3000, d55445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3001 q = 1) (hb : d61810 q = 1) : d55446 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3001, d55446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3001, d55446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3002 q = 1) (hb : d61810 q = 1) : d55447 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3002, d55447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3002, d55447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3003 q = 1) (hb : d61810 q = 1) : d55448 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3003, d55448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3003, d55448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2841 (p : Pattern) (ha : d3009 p = 1) (hb : d61810 p = 1) : d55454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3004 q = 1) (hb : d61810 q = 1) : d55449 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3004, d55449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2840 q ha hb
    | true =>
      simp only [d3004, d55449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3005 q = 1) (hb : d61810 q = 1) : d55450 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3005, d55450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3005, d55450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3006 q = 1) (hb : d61810 q = 1) : d55451 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3006, d55451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3006, d55451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3007 q = 1) (hb : d61810 q = 1) : d55452 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3007, d55452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3007, d55452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3008 q = 1) (hb : d61810 q = 1) : d55453 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3008, d55453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3008, d55453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3009 q = 1) (hb : d61810 q = 1) : d55454 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3009, d55454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3009, d55454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2842 (p : Pattern) (ha : d3015 p = 1) (hb : d61810 p = 1) : d55460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3010 q = 1) (hb : d61810 q = 1) : d55455 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3010, d55455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2841 q ha hb
    | true =>
      simp only [d3010, d55455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3011 q = 1) (hb : d61810 q = 1) : d55456 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3011, d55456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3011, d55456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3012 q = 1) (hb : d61810 q = 1) : d55457 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3012, d55457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3012, d55457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3013 q = 1) (hb : d61810 q = 1) : d55458 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3013, d55458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3013, d55458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3014 q = 1) (hb : d61810 q = 1) : d55459 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3014, d55459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3014, d55459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3015 q = 1) (hb : d61810 q = 1) : d55460 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3015, d55460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3015, d55460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2843 (p : Pattern) (ha : d1 p = 1) (hb : d55460 p = 1) : d55460 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d55460 q = 1) : d55460 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro2844 (p : Pattern) (ha : d0 p = 1) (hb : d61810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d61810 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2845 (p : Pattern) (ha : d3015 p = 1) (hb : d56770 p = 1) : d3015 p = 1 := by
  have h0 (q : Pattern) (ha : d3015 q = 1) (hb : d56770 q = 1) : d3015 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2846 (p : Pattern) (ha : d0 p = 1) (hb : d56770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56770 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2847 (p : Pattern) (ha : d3015 p = 1) (hb : d55757 p = 1) : d3015 p = 1 := by
  have h0 (q : Pattern) (ha : d3015 q = 1) (hb : d55757 q = 1) : d3015 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2848 (p : Pattern) (ha : d0 p = 1) (hb : d55757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55757 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2849 (p : Pattern) (ha : d213 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d103 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d213 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2850 (p : Pattern) (ha : d2898 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1018 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d114 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2896 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2896, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2896, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2525 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2849 q ha hb
  have h8 (q : Pattern) (ha : d2526 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2527 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2527, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d2528 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2528, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2528, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d2897 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2898 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2851 (p : Pattern) (ha : d2536 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d283 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2536 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2852 (p : Pattern) (ha : d2906 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1021 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d293 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d294 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2904 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2904, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2904, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2537 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2851 q ha hb
  have h8 (q : Pattern) (ha : d2538 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2539 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2539, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d2540 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2540, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2540, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d2905 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2906 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2853 (p : Pattern) (ha : d2912 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2899 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2850 q ha hb
  have h2 (q : Pattern) (ha : d2900 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2901 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2902 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2903 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2907 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2852 q ha hb
  have h7 (q : Pattern) (ha : d2908 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2909 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2910 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2911 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2912 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2854 (p : Pattern) (ha : d2549 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d496 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2549 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2855 (p : Pattern) (ha : d2915 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1025 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d509 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d510 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2913 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2913, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2913, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2550 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2854 q ha hb
  have h8 (q : Pattern) (ha : d2551 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2552 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2552, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d2553 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2553, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2553, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d2914 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2915 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2856 (p : Pattern) (ha : d2921 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2916 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2855 q ha hb
  have h2 (q : Pattern) (ha : d2917 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2918 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2919 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2920 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2921 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2857 (p : Pattern) (ha : d2563 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d788 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2563 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2858 (p : Pattern) (ha : d2925 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1029 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d801 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d802 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2923 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2923, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2923, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2564 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2857 q ha hb
  have h8 (q : Pattern) (ha : d2565 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2566 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2566, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d2567 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2567, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2567, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d2924 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2925 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2859 (p : Pattern) (ha : d2931 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2926 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2858 q ha hb
  have h2 (q : Pattern) (ha : d2927 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2928 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2929 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2930 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2931 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2860 (p : Pattern) (ha : d2578 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1166 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1167 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2578 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2861 (p : Pattern) (ha : d2936 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1033 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1180 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1181 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2934 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2934, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2934, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2579 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2860 q ha hb
  have h8 (q : Pattern) (ha : d2580 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2581 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2581, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d2582 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2582, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2582, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d2935 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2936 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2862 (p : Pattern) (ha : d2942 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2937 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2861 q ha hb
  have h2 (q : Pattern) (ha : d2938 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2939 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2940 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2941 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2942 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2863 (p : Pattern) (ha : d2594 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1627 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1628 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2594 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2864 (p : Pattern) (ha : d2948 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1037 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1641 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1642 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2946 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2946, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2946, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2595 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2863 q ha hb
  have h8 (q : Pattern) (ha : d2596 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2597 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2597, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d2598 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2598, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2598, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d2947 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2948 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2865 (p : Pattern) (ha : d2954 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2949 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2864 q ha hb
  have h2 (q : Pattern) (ha : d2950 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2951 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2952 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2953 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2954 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2866 (p : Pattern) (ha : d2611 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2111 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2611 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2867 (p : Pattern) (ha : d2961 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1041 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2124 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2125 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2959 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2959, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2959, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2612 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2866 q ha hb
  have h8 (q : Pattern) (ha : d2613 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2614 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2614, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h10 (q : Pattern) (ha : d2615 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2615, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2615, d64794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h11 (q : Pattern) (ha : d2960 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2961 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro2868 (p : Pattern) (ha : d2967 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2962 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2867 q ha hb
  have h2 (q : Pattern) (ha : d2963 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2964 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2965 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2966 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2967 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2869 (p : Pattern) (ha : d2973 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2922 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2853 q ha hb
    | true =>
      simp only [d2922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2856 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2932 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2859 q ha hb
  have h3 (q : Pattern) (ha : d2933 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2943 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2862 q ha hb
  have h5 (q : Pattern) (ha : d2944 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2945 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2955 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2865 q ha hb
  have h8 (q : Pattern) (ha : d2956 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2957 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2958 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2968 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2868 q ha hb
  have h12 (q : Pattern) (ha : d2969 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2970 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2971 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2972 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d2972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2973 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d2973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2870 (p : Pattern) (ha : d2979 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2974 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d2974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2869 q ha hb
    | true =>
      simp only [d2974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2975 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d2975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2976 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d2976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2977 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d2977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2978 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d2978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2979 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d2979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2871 (p : Pattern) (ha : d2985 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2980 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d2980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2870 q ha hb
    | true =>
      simp only [d2980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2981 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d2981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2982 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d2982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2983 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d2983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2984 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d2984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2985 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d2985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2872 (p : Pattern) (ha : d2991 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2986 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d2986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2871 q ha hb
    | true =>
      simp only [d2986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2987 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d2987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2988 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d2988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2989 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d2989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2990 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d2990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2991 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d2991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2873 (p : Pattern) (ha : d2997 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2992 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d2992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2872 q ha hb
    | true =>
      simp only [d2992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2993 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d2993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2994 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d2994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2995 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d2995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2996 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d2996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2997 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d2997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2874 (p : Pattern) (ha : d3003 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2998 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d2998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2873 q ha hb
    | true =>
      simp only [d2998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2999 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d2999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3000 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3001 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3002 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3003 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2875 (p : Pattern) (ha : d3009 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3004 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2874 q ha hb
    | true =>
      simp only [d3004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3005 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3006 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3007 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3008 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3009 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2876 (p : Pattern) (ha : d3015 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3010 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2875 q ha hb
    | true =>
      simp only [d3010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3011 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3012 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3013 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3014 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3015 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2877 (p : Pattern) (ha : d0 p = 1) (hb : d64963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64963 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2878 (p : Pattern) (ha : d0 p = 1) (hb : d64794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64794 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2879 (p : Pattern) (ha : d0 p = 1) (hb : d3842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3842 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2880 (p : Pattern) (ha : d2898 p = 1) (hb : d64965 p = 1) : d64968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d54978 q = 1) : d2525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1918 q ha hb
    | true =>
      simp only [d112, d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1919 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d54978 q = 1) : d2526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d54978 q = 1) : d3508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2896 q = 1) (hb : d64964 q = 1) : d64966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2896, d64964, d64966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2896, d64964, d64966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2528 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2897 q = 1) (hb : d64965 q = 1) : d64967 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2897, d64965, d64967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2897, d64965, d64967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2898 q = 1) (hb : d64965 q = 1) : d64968 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2898, d64968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2898, d64968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2881 (p : Pattern) (ha : d2906 p = 1) (hb : d64965 p = 1) : d64976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d54978 q = 1) : d2537 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1923 q ha hb
    | true =>
      simp only [d292, d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1924 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d54978 q = 1) : d2538 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d54978 q = 1) : d3521 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2904 q = 1) (hb : d64964 q = 1) : d64974 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2904, d64964, d64974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2904, d64964, d64974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2540 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2905 q = 1) (hb : d64965 q = 1) : d64975 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2905, d64965, d64975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2905, d64965, d64975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2906 q = 1) (hb : d64965 q = 1) : d64976 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2906, d64976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2906, d64976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2882 (p : Pattern) (ha : d2912 p = 1) (hb : d64965 p = 1) : d64982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2899 q = 1) (hb : d64965 q = 1) : d64969 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2899, d64969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2899, d64969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2880 q ha hb
  have h2 (q : Pattern) (ha : d2900 q = 1) (hb : d64965 q = 1) : d64970 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2900, d64970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2900, d64970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2901 q = 1) (hb : d64965 q = 1) : d64971 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2901, d64971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2901, d64971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2902 q = 1) (hb : d64965 q = 1) : d64972 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2902, d64972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2902, d64972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2903 q = 1) (hb : d64965 q = 1) : d64973 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2903, d64973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2903, d64973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2907 q = 1) (hb : d64965 q = 1) : d64977 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2907, d64977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2907, d64977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2881 q ha hb
  have h7 (q : Pattern) (ha : d2908 q = 1) (hb : d64965 q = 1) : d64978 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2908, d64978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2908, d64978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2909 q = 1) (hb : d64965 q = 1) : d64979 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2909, d64979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2909, d64979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2910 q = 1) (hb : d64965 q = 1) : d64980 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2910, d64980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2910, d64980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2911 q = 1) (hb : d64965 q = 1) : d64981 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2911, d64981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2911, d64981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2912 q = 1) (hb : d64965 q = 1) : d64982 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2912, d64982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2912, d64982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2883 (p : Pattern) (ha : d2915 p = 1) (hb : d64965 p = 1) : d64985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d54978 q = 1) : d2550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1930 q ha hb
    | true =>
      simp only [d508, d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1931 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d54978 q = 1) : d2551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d54978 q = 1) : d3536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2913 q = 1) (hb : d64964 q = 1) : d64983 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2913, d64964, d64983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2913, d64964, d64983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2553 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2914 q = 1) (hb : d64965 q = 1) : d64984 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2914, d64965, d64984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2914, d64965, d64984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2915 q = 1) (hb : d64965 q = 1) : d64985 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2915, d64985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2915, d64985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2884 (p : Pattern) (ha : d2921 p = 1) (hb : d64965 p = 1) : d64991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2916 q = 1) (hb : d64965 q = 1) : d64986 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2916, d64986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2916, d64986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2883 q ha hb
  have h2 (q : Pattern) (ha : d2917 q = 1) (hb : d64965 q = 1) : d64987 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2917, d64987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2917, d64987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2918 q = 1) (hb : d64965 q = 1) : d64988 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2918, d64988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2918, d64988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2919 q = 1) (hb : d64965 q = 1) : d64989 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2919, d64989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2919, d64989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2920 q = 1) (hb : d64965 q = 1) : d64990 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2920, d64990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2920, d64990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2921 q = 1) (hb : d64965 q = 1) : d64991 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2921, d64991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2921, d64991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2885 (p : Pattern) (ha : d2925 p = 1) (hb : d64965 p = 1) : d64995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d54978 q = 1) : d2564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1938 q ha hb
    | true =>
      simp only [d800, d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1939 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d54978 q = 1) : d2565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d54978 q = 1) : d3553 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2923 q = 1) (hb : d64964 q = 1) : d64993 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2923, d64964, d64993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2923, d64964, d64993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2567 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2924 q = 1) (hb : d64965 q = 1) : d64994 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2924, d64965, d64994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2924, d64965, d64994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2925 q = 1) (hb : d64965 q = 1) : d64995 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2925, d64995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2925, d64995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2886 (p : Pattern) (ha : d2931 p = 1) (hb : d64965 p = 1) : d65001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2926 q = 1) (hb : d64965 q = 1) : d64996 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2926, d64996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2926, d64996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2885 q ha hb
  have h2 (q : Pattern) (ha : d2927 q = 1) (hb : d64965 q = 1) : d64997 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2927, d64997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2927, d64997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2928 q = 1) (hb : d64965 q = 1) : d64998 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2928, d64998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2928, d64998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2929 q = 1) (hb : d64965 q = 1) : d64999 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2929, d64999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2929, d64999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2930 q = 1) (hb : d64965 q = 1) : d65000 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2930, d65000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2930, d65000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2931 q = 1) (hb : d64965 q = 1) : d65001 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2931, d65001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2931, d65001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2887 (p : Pattern) (ha : d2936 p = 1) (hb : d64965 p = 1) : d65006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d54978 q = 1) : d2579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1946 q ha hb
    | true =>
      simp only [d1179, d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1947 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d54978 q = 1) : d2580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d54978 q = 1) : d3571 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2934 q = 1) (hb : d64964 q = 1) : d65004 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2934, d64964, d65004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2934, d64964, d65004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2582 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2935 q = 1) (hb : d64965 q = 1) : d65005 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2935, d64965, d65005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2935, d64965, d65005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2936 q = 1) (hb : d64965 q = 1) : d65006 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2936, d65006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2936, d65006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2888 (p : Pattern) (ha : d2942 p = 1) (hb : d64965 p = 1) : d65012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2937 q = 1) (hb : d64965 q = 1) : d65007 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2937, d65007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2937, d65007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2887 q ha hb
  have h2 (q : Pattern) (ha : d2938 q = 1) (hb : d64965 q = 1) : d65008 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2938, d65008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2938, d65008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2939 q = 1) (hb : d64965 q = 1) : d65009 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2939, d65009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2939, d65009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2940 q = 1) (hb : d64965 q = 1) : d65010 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2940, d65010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2940, d65010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2941 q = 1) (hb : d64965 q = 1) : d65011 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2941, d65011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2941, d65011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2942 q = 1) (hb : d64965 q = 1) : d65012 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2942, d65012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2942, d65012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2889 (p : Pattern) (ha : d2948 p = 1) (hb : d64965 p = 1) : d65018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d54978 q = 1) : d2595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1954 q ha hb
    | true =>
      simp only [d1640, d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1955 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d54978 q = 1) : d2596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d54978 q = 1) : d3590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2946 q = 1) (hb : d64964 q = 1) : d65016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2946, d64964, d65016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2946, d64964, d65016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2598 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2947 q = 1) (hb : d64965 q = 1) : d65017 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2947, d64965, d65017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2947, d64965, d65017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2948 q = 1) (hb : d64965 q = 1) : d65018 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2948, d65018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2948, d65018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2890 (p : Pattern) (ha : d2954 p = 1) (hb : d64965 p = 1) : d65024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2949 q = 1) (hb : d64965 q = 1) : d65019 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2949, d65019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2949, d65019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2889 q ha hb
  have h2 (q : Pattern) (ha : d2950 q = 1) (hb : d64965 q = 1) : d65020 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2950, d65020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2950, d65020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2951 q = 1) (hb : d64965 q = 1) : d65021 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2951, d65021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2951, d65021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2952 q = 1) (hb : d64965 q = 1) : d65022 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2952, d65022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2952, d65022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2953 q = 1) (hb : d64965 q = 1) : d65023 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2953, d65023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2953, d65023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2954 q = 1) (hb : d64965 q = 1) : d65024 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2954, d65024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2954, d65024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2891 (p : Pattern) (ha : d2961 p = 1) (hb : d64965 p = 1) : d65031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d54978 q = 1) : d2612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1962 q ha hb
    | true =>
      simp only [d2123, d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1963 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d54978 q = 1) : d2613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d54978 q = 1) : d3610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2959 q = 1) (hb : d64964 q = 1) : d65029 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2959, d64964, d65029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2959, d64964, d65029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2615 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2960 q = 1) (hb : d64965 q = 1) : d65030 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2960, d64965, d65030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2960, d64965, d65030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2961 q = 1) (hb : d64965 q = 1) : d65031 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2961, d65031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2961, d65031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2892 (p : Pattern) (ha : d2967 p = 1) (hb : d64965 p = 1) : d65037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2962 q = 1) (hb : d64965 q = 1) : d65032 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2962, d65032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2962, d65032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2891 q ha hb
  have h2 (q : Pattern) (ha : d2963 q = 1) (hb : d64965 q = 1) : d65033 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2963, d65033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2963, d65033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2964 q = 1) (hb : d64965 q = 1) : d65034 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2964, d65034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2964, d65034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2965 q = 1) (hb : d64965 q = 1) : d65035 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2965, d65035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2965, d65035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2966 q = 1) (hb : d64965 q = 1) : d65036 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2966, d65036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2966, d65036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2967 q = 1) (hb : d64965 q = 1) : d65037 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2967, d65037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2967, d65037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2893 (p : Pattern) (ha : d2973 p = 1) (hb : d64965 p = 1) : d65043 p = 1 := by
  have h0 (q : Pattern) (ha : d2922 q = 1) (hb : d64965 q = 1) : d64992 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2922, d64992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2882 q ha hb
    | true =>
      simp only [d2922, d64992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2884 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2932 q = 1) (hb : d64965 q = 1) : d65002 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2932, d65002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2932, d65002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2886 q ha hb
  have h3 (q : Pattern) (ha : d2933 q = 1) (hb : d64965 q = 1) : d65003 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2933, d65003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2933, d65003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2943 q = 1) (hb : d64965 q = 1) : d65013 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2943, d65013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2943, d65013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2888 q ha hb
  have h5 (q : Pattern) (ha : d2944 q = 1) (hb : d64965 q = 1) : d65014 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2944, d65014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2944, d65014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2945 q = 1) (hb : d64965 q = 1) : d65015 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2945, d65015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2945, d65015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2955 q = 1) (hb : d64965 q = 1) : d65025 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2955, d65025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2955, d65025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2890 q ha hb
  have h8 (q : Pattern) (ha : d2956 q = 1) (hb : d64965 q = 1) : d65026 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2956, d65026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2956, d65026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2957 q = 1) (hb : d64965 q = 1) : d65027 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2957, d65027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2957, d65027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2958 q = 1) (hb : d64965 q = 1) : d65028 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2958, d65028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2958, d65028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2968 q = 1) (hb : d64965 q = 1) : d65038 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2968, d65038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2968, d65038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2892 q ha hb
  have h12 (q : Pattern) (ha : d2969 q = 1) (hb : d64965 q = 1) : d65039 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2969, d65039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2969, d65039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2970 q = 1) (hb : d64965 q = 1) : d65040 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2970, d65040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2970, d65040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2971 q = 1) (hb : d64965 q = 1) : d65041 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2971, d65041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2971, d65041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2972 q = 1) (hb : d64965 q = 1) : d65042 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d2972, d65042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2972, d65042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2973 q = 1) (hb : d64965 q = 1) : d65043 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d2973, d65043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d2973, d65043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2894 (p : Pattern) (ha : d2979 p = 1) (hb : d64965 p = 1) : d65049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2974 q = 1) (hb : d64965 q = 1) : d65044 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d2974, d65044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2893 q ha hb
    | true =>
      simp only [d2974, d65044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2975 q = 1) (hb : d64965 q = 1) : d65045 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d2975, d65045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2975, d65045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2976 q = 1) (hb : d64965 q = 1) : d65046 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d2976, d65046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2976, d65046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2977 q = 1) (hb : d64965 q = 1) : d65047 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d2977, d65047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2977, d65047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2978 q = 1) (hb : d64965 q = 1) : d65048 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d2978, d65048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2978, d65048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2979 q = 1) (hb : d64965 q = 1) : d65049 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d2979, d65049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2979, d65049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2895 (p : Pattern) (ha : d2985 p = 1) (hb : d64965 p = 1) : d65055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2980 q = 1) (hb : d64965 q = 1) : d65050 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d2980, d65050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2894 q ha hb
    | true =>
      simp only [d2980, d65050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2981 q = 1) (hb : d64965 q = 1) : d65051 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d2981, d65051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2981, d65051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2982 q = 1) (hb : d64965 q = 1) : d65052 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d2982, d65052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2982, d65052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2983 q = 1) (hb : d64965 q = 1) : d65053 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d2983, d65053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2983, d65053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2984 q = 1) (hb : d64965 q = 1) : d65054 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d2984, d65054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2984, d65054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2985 q = 1) (hb : d64965 q = 1) : d65055 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d2985, d65055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2985, d65055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2896 (p : Pattern) (ha : d2991 p = 1) (hb : d64965 p = 1) : d65061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2986 q = 1) (hb : d64965 q = 1) : d65056 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d2986, d65056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2895 q ha hb
    | true =>
      simp only [d2986, d65056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2987 q = 1) (hb : d64965 q = 1) : d65057 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d2987, d65057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2987, d65057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2988 q = 1) (hb : d64965 q = 1) : d65058 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d2988, d65058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2988, d65058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2989 q = 1) (hb : d64965 q = 1) : d65059 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d2989, d65059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2989, d65059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2990 q = 1) (hb : d64965 q = 1) : d65060 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d2990, d65060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2990, d65060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2991 q = 1) (hb : d64965 q = 1) : d65061 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d2991, d65061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2991, d65061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2897 (p : Pattern) (ha : d2997 p = 1) (hb : d64965 p = 1) : d65067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2992 q = 1) (hb : d64965 q = 1) : d65062 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d2992, d65062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2896 q ha hb
    | true =>
      simp only [d2992, d65062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2993 q = 1) (hb : d64965 q = 1) : d65063 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d2993, d65063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2993, d65063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2994 q = 1) (hb : d64965 q = 1) : d65064 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d2994, d65064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2994, d65064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2995 q = 1) (hb : d64965 q = 1) : d65065 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d2995, d65065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2995, d65065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2996 q = 1) (hb : d64965 q = 1) : d65066 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d2996, d65066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2996, d65066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2997 q = 1) (hb : d64965 q = 1) : d65067 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d2997, d65067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2997, d65067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2898 (p : Pattern) (ha : d3003 p = 1) (hb : d64965 p = 1) : d65073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2998 q = 1) (hb : d64965 q = 1) : d65068 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d2998, d65068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2897 q ha hb
    | true =>
      simp only [d2998, d65068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2999 q = 1) (hb : d64965 q = 1) : d65069 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d2999, d65069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2999, d65069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3000 q = 1) (hb : d64965 q = 1) : d65070 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3000, d65070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3000, d65070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3001 q = 1) (hb : d64965 q = 1) : d65071 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3001, d65071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3001, d65071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3002 q = 1) (hb : d64965 q = 1) : d65072 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3002, d65072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3002, d65072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3003 q = 1) (hb : d64965 q = 1) : d65073 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3003, d65073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3003, d65073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2899 (p : Pattern) (ha : d3009 p = 1) (hb : d64965 p = 1) : d65079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3004 q = 1) (hb : d64965 q = 1) : d65074 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3004, d65074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2898 q ha hb
    | true =>
      simp only [d3004, d65074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3005 q = 1) (hb : d64965 q = 1) : d65075 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3005, d65075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3005, d65075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3006 q = 1) (hb : d64965 q = 1) : d65076 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3006, d65076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3006, d65076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3007 q = 1) (hb : d64965 q = 1) : d65077 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3007, d65077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3007, d65077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3008 q = 1) (hb : d64965 q = 1) : d65078 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3008, d65078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3008, d65078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3009 q = 1) (hb : d64965 q = 1) : d65079 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3009, d65079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3009, d65079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2900 (p : Pattern) (ha : d3015 p = 1) (hb : d64965 p = 1) : d65085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3010 q = 1) (hb : d64965 q = 1) : d65080 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3010, d65080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2899 q ha hb
    | true =>
      simp only [d3010, d65080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3011 q = 1) (hb : d64965 q = 1) : d65081 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3011, d65081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3011, d65081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3012 q = 1) (hb : d64965 q = 1) : d65082 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3012, d65082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3012, d65082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3013 q = 1) (hb : d64965 q = 1) : d65083 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3013, d65083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3013, d65083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3014 q = 1) (hb : d64965 q = 1) : d65084 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3014, d65084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3014, d65084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3015 q = 1) (hb : d64965 q = 1) : d65085 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3015, d65085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3015, d65085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2901 (p : Pattern) (ha : d62395 p = 1) (hb : d64968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2525 q = 1) (hb : d55598 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
  have h2 (q : Pattern) (ha : d2526 q = 1) (hb : d55599 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3508 q = 1) (hb : d62388 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, d62388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3508, d62388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d62392 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62393 q = 1) (hb : d64966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62393, d64966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d62393, d64966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d62394 q = 1) (hb : d64967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62394, d64967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62394, d64967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d62395 q = 1) (hb : d64968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62395, d64968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62395, d64968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro2902 (p : Pattern) (ha : d62409 p = 1) (hb : d64976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2537 q = 1) (hb : d55610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro697 q ha hb
  have h2 (q : Pattern) (ha : d2538 q = 1) (hb : d55611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3521 q = 1) (hb : d62401 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, d62401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3521, d62401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d62406 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62407 q = 1) (hb : d64974 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62407, d64974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d62407, d64974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d62408 q = 1) (hb : d64975 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62408, d64975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62408, d64975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d62409 q = 1) (hb : d64976 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62409, d64976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62409, d64976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro2903 (p : Pattern) (ha : d62415 p = 1) (hb : d64982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62396 q = 1) (hb : d64969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62396, d64969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62396, d64969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2901 q ha hb
  have h3 (q : Pattern) (ha : d62397 q = 1) (hb : d64970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62397, d64970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62397, d64970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62398 q = 1) (hb : d64971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62398, d64971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62398, d64971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62399 q = 1) (hb : d64972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62399, d64972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62399, d64972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62400 q = 1) (hb : d64973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62400, d64973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62400, d64973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62410 q = 1) (hb : d64977 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62410, d64977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62410, d64977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2902 q ha hb
  have h8 (q : Pattern) (ha : d62411 q = 1) (hb : d64978 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62411, d64978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62411, d64978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62412 q = 1) (hb : d64979 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62412, d64979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62412, d64979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62413 q = 1) (hb : d64980 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62413, d64980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62413, d64980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62414 q = 1) (hb : d64981 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62414, d64981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62414, d64981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62415 q = 1) (hb : d64982 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62415, d64982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62415, d64982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro2904 (p : Pattern) (ha : d62425 p = 1) (hb : d64985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2550 q = 1) (hb : d55623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro700 q ha hb
  have h2 (q : Pattern) (ha : d2551 q = 1) (hb : d55624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3536 q = 1) (hb : d62416 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, d62416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3536, d62416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d62422 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62423 q = 1) (hb : d64983 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62423, d64983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d62423, d64983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d62424 q = 1) (hb : d64984 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62424, d64984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62424, d64984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d62425 q = 1) (hb : d64985 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62425, d64985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62425, d64985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro2905 (p : Pattern) (ha : d62431 p = 1) (hb : d64991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62426 q = 1) (hb : d64986 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62426, d64986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62426, d64986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2904 q ha hb
  have h2 (q : Pattern) (ha : d62427 q = 1) (hb : d64987 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62427, d64987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62427, d64987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62428 q = 1) (hb : d64988 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62428, d64988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62428, d64988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62429 q = 1) (hb : d64989 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62429, d64989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62429, d64989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62430 q = 1) (hb : d64990 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62430, d64990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62430, d64990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62431 q = 1) (hb : d64991 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62431, d64991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62431, d64991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2906 (p : Pattern) (ha : d62442 p = 1) (hb : d64995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2564 q = 1) (hb : d55637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro703 q ha hb
  have h2 (q : Pattern) (ha : d2565 q = 1) (hb : d55638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3553 q = 1) (hb : d62433 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, d62433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3553, d62433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d62439 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62440 q = 1) (hb : d64993 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62440, d64993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d62440, d64993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d62441 q = 1) (hb : d64994 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62441, d64994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62441, d64994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d62442 q = 1) (hb : d64995 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62442, d64995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62442, d64995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro2907 (p : Pattern) (ha : d62448 p = 1) (hb : d65001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62443 q = 1) (hb : d64996 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62443, d64996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62443, d64996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2906 q ha hb
  have h2 (q : Pattern) (ha : d62444 q = 1) (hb : d64997 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62444, d64997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62444, d64997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62445 q = 1) (hb : d64998 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62445, d64998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62445, d64998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62446 q = 1) (hb : d64999 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62446, d64999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62446, d64999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62447 q = 1) (hb : d65000 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62447, d65000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62447, d65000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62448 q = 1) (hb : d65001 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62448, d65001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62448, d65001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2908 (p : Pattern) (ha : d62460 p = 1) (hb : d65006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2579 q = 1) (hb : d55652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro706 q ha hb
  have h2 (q : Pattern) (ha : d2580 q = 1) (hb : d55653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3571 q = 1) (hb : d62451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, d62451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3571, d62451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d62457 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62458 q = 1) (hb : d65004 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62458, d65004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d62458, d65004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d62459 q = 1) (hb : d65005 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62459, d65005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62459, d65005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d62460 q = 1) (hb : d65006 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62460, d65006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62460, d65006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro2909 (p : Pattern) (ha : d62466 p = 1) (hb : d65012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62461 q = 1) (hb : d65007 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62461, d65007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62461, d65007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2908 q ha hb
  have h2 (q : Pattern) (ha : d62462 q = 1) (hb : d65008 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62462, d65008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62462, d65008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62463 q = 1) (hb : d65009 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62463, d65009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62463, d65009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62464 q = 1) (hb : d65010 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62464, d65010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62464, d65010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62465 q = 1) (hb : d65011 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62465, d65011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62465, d65011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62466 q = 1) (hb : d65012 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62466, d65012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62466, d65012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2910 (p : Pattern) (ha : d62479 p = 1) (hb : d65018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2595 q = 1) (hb : d55668 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro709 q ha hb
  have h2 (q : Pattern) (ha : d2596 q = 1) (hb : d55669 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3590 q = 1) (hb : d62470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, d62470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3590, d62470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d62476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62477 q = 1) (hb : d65016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62477, d65016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d62477, d65016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d62478 q = 1) (hb : d65017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62478, d65017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62478, d65017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d62479 q = 1) (hb : d65018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62479, d65018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62479, d65018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro2911 (p : Pattern) (ha : d62485 p = 1) (hb : d65024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62480 q = 1) (hb : d65019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62480, d65019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62480, d65019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2910 q ha hb
  have h2 (q : Pattern) (ha : d62481 q = 1) (hb : d65020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62481, d65020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62481, d65020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62482 q = 1) (hb : d65021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62482, d65021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62482, d65021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62483 q = 1) (hb : d65022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62483, d65022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62483, d65022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62484 q = 1) (hb : d65023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62484, d65023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62484, d65023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62485 q = 1) (hb : d65024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62485, d65024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62485, d65024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2912 (p : Pattern) (ha : d62499 p = 1) (hb : d65031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2612 q = 1) (hb : d55685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro712 q ha hb
  have h2 (q : Pattern) (ha : d2613 q = 1) (hb : d55686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3610 q = 1) (hb : d62490 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, d62490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, d62490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d62496 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d62497 q = 1) (hb : d65029 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62497, d65029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d62497, d65029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d62498 q = 1) (hb : d65030 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62498, d65030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62498, d65030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d62499 q = 1) (hb : d65031 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62499, d65031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62499, d65031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro2913 (p : Pattern) (ha : d62505 p = 1) (hb : d65037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62500 q = 1) (hb : d65032 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62500, d65032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62500, d65032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2912 q ha hb
  have h2 (q : Pattern) (ha : d62501 q = 1) (hb : d65033 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62501, d65033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62501, d65033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62502 q = 1) (hb : d65034 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62502, d65034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62502, d65034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62503 q = 1) (hb : d65035 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62503, d65035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62503, d65035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62504 q = 1) (hb : d65036 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62504, d65036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62504, d65036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62505 q = 1) (hb : d65037 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62505, d65037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62505, d65037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2914 (p : Pattern) (ha : d62511 p = 1) (hb : d65043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62432 q = 1) (hb : d64992 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62432, d64992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2903 q ha hb
    | true =>
      simp only [d62432, d64992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2905 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62449 q = 1) (hb : d65002 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62449, d65002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62449, d65002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2907 q ha hb
  have h3 (q : Pattern) (ha : d62450 q = 1) (hb : d65003 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62450, d65003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62450, d65003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62467 q = 1) (hb : d65013 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62467, d65013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62467, d65013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2909 q ha hb
  have h5 (q : Pattern) (ha : d62468 q = 1) (hb : d65014 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62468, d65014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62468, d65014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62469 q = 1) (hb : d65015 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62469, d65015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62469, d65015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62486 q = 1) (hb : d65025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62486, d65025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62486, d65025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2911 q ha hb
  have h8 (q : Pattern) (ha : d62487 q = 1) (hb : d65026 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62487, d65026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62487, d65026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62488 q = 1) (hb : d65027 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62488, d65027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62488, d65027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62489 q = 1) (hb : d65028 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62489, d65028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62489, d65028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62506 q = 1) (hb : d65038 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62506, d65038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62506, d65038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2913 q ha hb
  have h12 (q : Pattern) (ha : d62507 q = 1) (hb : d65039 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62507, d65039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62507, d65039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62508 q = 1) (hb : d65040 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62508, d65040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62508, d65040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62509 q = 1) (hb : d65041 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62509, d65041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62509, d65041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62510 q = 1) (hb : d65042 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62510, d65042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62510, d65042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62511 q = 1) (hb : d65043 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62511, d65043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62511, d65043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro2915 (p : Pattern) (ha : d62517 p = 1) (hb : d65049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62512 q = 1) (hb : d65044 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62512, d65044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2914 q ha hb
    | true =>
      simp only [d62512, d65044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62513 q = 1) (hb : d65045 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62513, d65045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62513, d65045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62514 q = 1) (hb : d65046 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62514, d65046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62514, d65046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62515 q = 1) (hb : d65047 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62515, d65047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62515, d65047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62516 q = 1) (hb : d65048 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62516, d65048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62516, d65048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62517 q = 1) (hb : d65049 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62517, d65049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62517, d65049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2916 (p : Pattern) (ha : d62523 p = 1) (hb : d65055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62518 q = 1) (hb : d65050 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62518, d65050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2915 q ha hb
    | true =>
      simp only [d62518, d65050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62519 q = 1) (hb : d65051 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62519, d65051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62519, d65051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62520 q = 1) (hb : d65052 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62520, d65052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62520, d65052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62521 q = 1) (hb : d65053 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62521, d65053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62521, d65053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62522 q = 1) (hb : d65054 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62522, d65054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62522, d65054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62523 q = 1) (hb : d65055 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62523, d65055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62523, d65055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2917 (p : Pattern) (ha : d62529 p = 1) (hb : d65061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62524 q = 1) (hb : d65056 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62524, d65056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2916 q ha hb
    | true =>
      simp only [d62524, d65056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62525 q = 1) (hb : d65057 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62525, d65057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62525, d65057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62526 q = 1) (hb : d65058 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62526, d65058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62526, d65058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62527 q = 1) (hb : d65059 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62527, d65059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62527, d65059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62528 q = 1) (hb : d65060 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62528, d65060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62528, d65060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62529 q = 1) (hb : d65061 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62529, d65061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62529, d65061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2918 (p : Pattern) (ha : d62535 p = 1) (hb : d65067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62530 q = 1) (hb : d65062 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62530, d65062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2917 q ha hb
    | true =>
      simp only [d62530, d65062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62531 q = 1) (hb : d65063 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62531, d65063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62531, d65063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62532 q = 1) (hb : d65064 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62532, d65064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62532, d65064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62533 q = 1) (hb : d65065 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62533, d65065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62533, d65065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62534 q = 1) (hb : d65066 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62534, d65066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62534, d65066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62535 q = 1) (hb : d65067 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62535, d65067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62535, d65067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2919 (p : Pattern) (ha : d62541 p = 1) (hb : d65073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62536 q = 1) (hb : d65068 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62536, d65068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2918 q ha hb
    | true =>
      simp only [d62536, d65068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62537 q = 1) (hb : d65069 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62537, d65069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62537, d65069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62538 q = 1) (hb : d65070 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62538, d65070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62538, d65070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62539 q = 1) (hb : d65071 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62539, d65071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62539, d65071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62540 q = 1) (hb : d65072 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62540, d65072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62540, d65072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62541 q = 1) (hb : d65073 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62541, d65073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62541, d65073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2920 (p : Pattern) (ha : d62547 p = 1) (hb : d65079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62542 q = 1) (hb : d65074 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62542, d65074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2919 q ha hb
    | true =>
      simp only [d62542, d65074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62543 q = 1) (hb : d65075 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62543, d65075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62543, d65075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62544 q = 1) (hb : d65076 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62544, d65076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62544, d65076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62545 q = 1) (hb : d65077 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62545, d65077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62545, d65077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62546 q = 1) (hb : d65078 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62546, d65078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62546, d65078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62547 q = 1) (hb : d65079 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62547, d65079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62547, d65079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2921 (p : Pattern) (ha : d62553 p = 1) (hb : d65085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62548 q = 1) (hb : d65080 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62548, d65080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2920 q ha hb
    | true =>
      simp only [d62548, d65080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d62549 q = 1) (hb : d65081 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62549, d65081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62549, d65081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d62550 q = 1) (hb : d65082 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62550, d65082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62550, d65082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d62551 q = 1) (hb : d65083 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62551, d65083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62551, d65083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d62552 q = 1) (hb : d65084 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62552, d65084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62552, d65084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d62553 q = 1) (hb : d65085 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62553, d65085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62553, d65085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2922 (p : Pattern) (ha : d0 p = 1) (hb : d64965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64965 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2923 (p : Pattern) (ha : d0 p = 1) (hb : d62553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62553 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2924 (p : Pattern) (ha : d0 p = 1) (hb : d62701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62701 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2925 (p : Pattern) (ha : d56141 p = 1) (hb : d56148 p = 1) : d56141 p = 1 := by
  have h0 (q : Pattern) (ha : d56141 q = 1) (hb : d56148 q = 1) : d56141 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro2926 (p : Pattern) (ha : d55603 p = 1) (hb : d56024 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3016 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3016, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3016, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51647 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q ha hb
    | true =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34 q ha hb
  have h6 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51648 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51648, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51649 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51649, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52035 q = 1) (hb : d56022 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d56022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52035, d56022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2525 q = 1) (hb : d55598 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
  have h11 (q : Pattern) (ha : d2526 q = 1) (hb : d55599 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2527 q = 1) (hb : d55600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d55600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2527, d55600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2528 q = 1) (hb : d55601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2528, d55601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2528, d55601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d55602 q = 1) (hb : d56023 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55602, d56023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55602, d56023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d55603 q = 1) (hb : d56024 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55603, d56024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d55603, d56024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro2927 (p : Pattern) (ha : d55615 p = 1) (hb : d56032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3025 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3025, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3025, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51664 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q ha hb
    | true =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57 q ha hb
  have h6 (q : Pattern) (ha : d398 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38 q ha hb
    | true =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h7 (q : Pattern) (ha : d51665 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51665, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51666 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51666, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52167 q = 1) (hb : d56030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d56030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52167, d56030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2537 q = 1) (hb : d55610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro697 q ha hb
  have h11 (q : Pattern) (ha : d2538 q = 1) (hb : d55611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2539 q = 1) (hb : d55612 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d55612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2539, d55612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2540 q = 1) (hb : d55613 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2540, d55613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2540, d55613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d55614 q = 1) (hb : d56031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55614, d56031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55614, d56031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d55615 q = 1) (hb : d56032 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55615, d56032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d55615, d56032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro2928 (p : Pattern) (ha : d55621 p = 1) (hb : d56038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d54634 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, d54634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, d54634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro557 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d54635 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, d54635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, d54635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d54636 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, d54636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, d54636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, d54637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, d54637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55604 q = 1) (hb : d56025 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55604, d56025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55604, d56025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2926 q ha hb
  have h6 (q : Pattern) (ha : d55605 q = 1) (hb : d56026 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55605, d56026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55605, d56026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d55606 q = 1) (hb : d56027 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55606, d56027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55606, d56027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d55607 q = 1) (hb : d56028 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55607, d56028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55607, d56028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d55608 q = 1) (hb : d56029 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55608, d56029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d55608, d56029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d55616 q = 1) (hb : d56033 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55616, d56033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55616, d56033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2927 q ha hb
  have h11 (q : Pattern) (ha : d55617 q = 1) (hb : d56034 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55617, d56034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55617, d56034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d55618 q = 1) (hb : d56035 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55618, d56035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55618, d56035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d55619 q = 1) (hb : d56036 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55619, d56036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55619, d56036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d55620 q = 1) (hb : d56037 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55620, d56037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55620, d56037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d55621 q = 1) (hb : d56038 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55621, d56038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55621, d56038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro2929 (p : Pattern) (ha : d55628 p = 1) (hb : d56041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3035 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3035, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3035, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51689 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q ha hb
    | true =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97 q ha hb
  have h6 (q : Pattern) (ha : d645 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro68 q ha hb
    | true =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q ha hb
  have h7 (q : Pattern) (ha : d51690 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51690, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51691 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51691, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52352 q = 1) (hb : d56039 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d56039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52352, d56039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2550 q = 1) (hb : d55623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro700 q ha hb
  have h11 (q : Pattern) (ha : d2551 q = 1) (hb : d55624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2552 q = 1) (hb : d55625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d55625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2552, d55625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2553 q = 1) (hb : d55626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2553, d55626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2553, d55626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d55627 q = 1) (hb : d56040 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55627, d56040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55627, d56040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d55628 q = 1) (hb : d56041 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55628, d56041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d55628, d56041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro2930 (p : Pattern) (ha : d55634 p = 1) (hb : d56047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55629 q = 1) (hb : d56042 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55629, d56042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55629, d56042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2929 q ha hb
  have h2 (q : Pattern) (ha : d55630 q = 1) (hb : d56043 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55630, d56043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55630, d56043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55631 q = 1) (hb : d56044 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55631, d56044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55631, d56044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55632 q = 1) (hb : d56045 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55632, d56045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55632, d56045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55633 q = 1) (hb : d56046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55633, d56046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55633, d56046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55634 q = 1) (hb : d56047 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55634, d56047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55634, d56047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2931 (p : Pattern) (ha : d55642 p = 1) (hb : d56051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3046 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3046, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3046, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51715 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q ha hb
    | true =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro144 q ha hb
  have h6 (q : Pattern) (ha : d951 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro112 q ha hb
    | true =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h7 (q : Pattern) (ha : d51716 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51716, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51717 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51717, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52573 q = 1) (hb : d56049 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d56049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52573, d56049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2564 q = 1) (hb : d55637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro703 q ha hb
  have h11 (q : Pattern) (ha : d2565 q = 1) (hb : d55638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2566 q = 1) (hb : d55639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d55639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2566, d55639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2567 q = 1) (hb : d55640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2567, d55640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2567, d55640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d55641 q = 1) (hb : d56050 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55641, d56050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55641, d56050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d55642 q = 1) (hb : d56051 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55642, d56051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d55642, d56051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro2932 (p : Pattern) (ha : d55648 p = 1) (hb : d56057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55643 q = 1) (hb : d56052 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55643, d56052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55643, d56052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2931 q ha hb
  have h2 (q : Pattern) (ha : d55644 q = 1) (hb : d56053 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55644, d56053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55644, d56053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55645 q = 1) (hb : d56054 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55645, d56054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55645, d56054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55646 q = 1) (hb : d56055 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55646, d56055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55646, d56055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55647 q = 1) (hb : d56056 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55647, d56056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55647, d56056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55648 q = 1) (hb : d56057 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55648, d56057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55648, d56057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2933 (p : Pattern) (ha : d55657 p = 1) (hb : d56062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3058 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3058, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3058, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51742 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q ha hb
    | true =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro196 q ha hb
  have h6 (q : Pattern) (ha : d1362 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro164 q ha hb
    | true =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h7 (q : Pattern) (ha : d51743 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51743, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51744 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51744, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52853 q = 1) (hb : d56060 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d56060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52853, d56060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2579 q = 1) (hb : d55652 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro706 q ha hb
  have h11 (q : Pattern) (ha : d2580 q = 1) (hb : d55653 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2581 q = 1) (hb : d55654 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d55654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2581, d55654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2582 q = 1) (hb : d55655 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2582, d55655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2582, d55655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d55656 q = 1) (hb : d56061 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55656, d56061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55656, d56061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d55657 q = 1) (hb : d56062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55657, d56062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d55657, d56062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro2934 (p : Pattern) (ha : d55663 p = 1) (hb : d56068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55658 q = 1) (hb : d56063 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55658, d56063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55658, d56063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2933 q ha hb
  have h2 (q : Pattern) (ha : d55659 q = 1) (hb : d56064 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55659, d56064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55659, d56064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55660 q = 1) (hb : d56065 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55660, d56065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55660, d56065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55661 q = 1) (hb : d56066 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55661, d56066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55661, d56066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55662 q = 1) (hb : d56067 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55662, d56067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55662, d56067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55663 q = 1) (hb : d56068 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55663, d56068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55663, d56068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2935 (p : Pattern) (ha : d55673 p = 1) (hb : d56074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3071 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3071, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3071, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51770 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q ha hb
    | true =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro252 q ha hb
  have h6 (q : Pattern) (ha : d1839 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro222 q ha hb
    | true =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h7 (q : Pattern) (ha : d51771 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51771, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51772 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51772, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53168 q = 1) (hb : d56072 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d56072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53168, d56072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2595 q = 1) (hb : d55668 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro709 q ha hb
  have h11 (q : Pattern) (ha : d2596 q = 1) (hb : d55669 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2597 q = 1) (hb : d55670 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d55670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2597, d55670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2598 q = 1) (hb : d55671 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2598, d55671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2598, d55671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d55672 q = 1) (hb : d56073 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55672, d56073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55672, d56073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d55673 q = 1) (hb : d56074 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55673, d56074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d55673, d56074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro2936 (p : Pattern) (ha : d55679 p = 1) (hb : d56080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55674 q = 1) (hb : d56075 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55674, d56075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55674, d56075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2935 q ha hb
  have h2 (q : Pattern) (ha : d55675 q = 1) (hb : d56076 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55675, d56076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55675, d56076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55676 q = 1) (hb : d56077 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55676, d56077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55676, d56077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55677 q = 1) (hb : d56078 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55677, d56078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55677, d56078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55678 q = 1) (hb : d56079 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55678, d56079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55678, d56079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55679 q = 1) (hb : d56080 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55679, d56080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55679, d56080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2937 (p : Pattern) (ha : d55690 p = 1) (hb : d56087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3085 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3085, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3085, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51799 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q ha hb
    | true =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro311 q ha hb
  have h6 (q : Pattern) (ha : d2317 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro281 q ha hb
    | true =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h7 (q : Pattern) (ha : d51800 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51800, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51801 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51801, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53485 q = 1) (hb : d56085 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d56085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53485, d56085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2612 q = 1) (hb : d55685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro712 q ha hb
  have h11 (q : Pattern) (ha : d2613 q = 1) (hb : d55686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2614 q = 1) (hb : d55687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d55687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2614, d55687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2615 q = 1) (hb : d55688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2615, d55688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2615, d55688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d55689 q = 1) (hb : d56086 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d55689, d56086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d55689, d56086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d55690 q = 1) (hb : d56087 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d55690, d56087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d55690, d56087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro2938 (p : Pattern) (ha : d55696 p = 1) (hb : d56093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55691 q = 1) (hb : d56088 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d55691, d56088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55691, d56088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2937 q ha hb
  have h2 (q : Pattern) (ha : d55692 q = 1) (hb : d56089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d55692, d56089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55692, d56089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d55693 q = 1) (hb : d56090 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d55693, d56090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55693, d56090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55694 q = 1) (hb : d56091 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d55694, d56091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55694, d56091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d55695 q = 1) (hb : d56092 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d55695, d56092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55695, d56092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55696 q = 1) (hb : d56093 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d55696, d56093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d55696, d56093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2939 (p : Pattern) (ha : d55702 p = 1) (hb : d56099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d55635 q = 1) (hb : d56048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55635, d56048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2928 q ha hb
    | true =>
      simp only [d55635, d56048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2930 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d55649 q = 1) (hb : d56058 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55649, d56058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55649, d56058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2932 q ha hb
  have h3 (q : Pattern) (ha : d55650 q = 1) (hb : d56059 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55650, d56059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d55650, d56059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d55664 q = 1) (hb : d56069 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55664, d56069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55664, d56069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2934 q ha hb
  have h5 (q : Pattern) (ha : d55665 q = 1) (hb : d56070 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55665, d56070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55665, d56070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d55666 q = 1) (hb : d56071 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55666, d56071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55666, d56071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d55680 q = 1) (hb : d56081 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55680, d56081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55680, d56081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2936 q ha hb
  have h8 (q : Pattern) (ha : d55681 q = 1) (hb : d56082 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55681, d56082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55681, d56082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d55682 q = 1) (hb : d56083 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55682, d56083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55682, d56083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d55683 q = 1) (hb : d56084 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d55683, d56084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d55683, d56084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55697 q = 1) (hb : d56094 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d55697, d56094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55697, d56094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2938 q ha hb
  have h12 (q : Pattern) (ha : d55698 q = 1) (hb : d56095 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d55698, d56095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55698, d56095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d55699 q = 1) (hb : d56096 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d55699, d56096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55699, d56096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d55700 q = 1) (hb : d56097 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d55700, d56097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d55700, d56097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d55701 q = 1) (hb : d56098 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d55701, d56098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d55701, d56098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d55702 q = 1) (hb : d56099 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d55702, d56099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d55702, d56099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro2940 (p : Pattern) (ha : d55708 p = 1) (hb : d56105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55703 q = 1) (hb : d56100 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d55703, d56100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2939 q ha hb
    | true =>
      simp only [d55703, d56100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55704 q = 1) (hb : d56101 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d55704, d56101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55704, d56101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55705 q = 1) (hb : d56102 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d55705, d56102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55705, d56102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55706 q = 1) (hb : d56103 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d55706, d56103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55706, d56103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55707 q = 1) (hb : d56104 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d55707, d56104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55707, d56104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55708 q = 1) (hb : d56105 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d55708, d56105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55708, d56105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2941 (p : Pattern) (ha : d55714 p = 1) (hb : d56111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55709 q = 1) (hb : d56106 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d55709, d56106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2940 q ha hb
    | true =>
      simp only [d55709, d56106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55710 q = 1) (hb : d56107 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d55710, d56107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55710, d56107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55711 q = 1) (hb : d56108 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d55711, d56108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55711, d56108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55712 q = 1) (hb : d56109 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d55712, d56109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55712, d56109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55713 q = 1) (hb : d56110 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d55713, d56110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55713, d56110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55714 q = 1) (hb : d56111 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d55714, d56111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55714, d56111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2942 (p : Pattern) (ha : d55720 p = 1) (hb : d56117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55715 q = 1) (hb : d56112 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d55715, d56112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2941 q ha hb
    | true =>
      simp only [d55715, d56112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55716 q = 1) (hb : d56113 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d55716, d56113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55716, d56113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55717 q = 1) (hb : d56114 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d55717, d56114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55717, d56114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55718 q = 1) (hb : d56115 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d55718, d56115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55718, d56115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55719 q = 1) (hb : d56116 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d55719, d56116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55719, d56116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55720 q = 1) (hb : d56117 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d55720, d56117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55720, d56117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2943 (p : Pattern) (ha : d55726 p = 1) (hb : d56123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55721 q = 1) (hb : d56118 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d55721, d56118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2942 q ha hb
    | true =>
      simp only [d55721, d56118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55722 q = 1) (hb : d56119 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d55722, d56119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55722, d56119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55723 q = 1) (hb : d56120 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d55723, d56120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55723, d56120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55724 q = 1) (hb : d56121 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d55724, d56121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55724, d56121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55725 q = 1) (hb : d56122 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d55725, d56122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55725, d56122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55726 q = 1) (hb : d56123 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d55726, d56123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55726, d56123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2944 (p : Pattern) (ha : d55732 p = 1) (hb : d56129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55727 q = 1) (hb : d56124 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d55727, d56124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2943 q ha hb
    | true =>
      simp only [d55727, d56124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55728 q = 1) (hb : d56125 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d55728, d56125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55728, d56125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55729 q = 1) (hb : d56126 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d55729, d56126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55729, d56126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55730 q = 1) (hb : d56127 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d55730, d56127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55730, d56127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55731 q = 1) (hb : d56128 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d55731, d56128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55731, d56128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55732 q = 1) (hb : d56129 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d55732, d56129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55732, d56129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2945 (p : Pattern) (ha : d55738 p = 1) (hb : d56135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55733 q = 1) (hb : d56130 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d55733, d56130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2944 q ha hb
    | true =>
      simp only [d55733, d56130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55734 q = 1) (hb : d56131 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d55734, d56131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55734, d56131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55735 q = 1) (hb : d56132 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d55735, d56132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55735, d56132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55736 q = 1) (hb : d56133 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d55736, d56133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55736, d56133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55737 q = 1) (hb : d56134 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d55737, d56134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55737, d56134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55738 q = 1) (hb : d56135 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d55738, d56135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55738, d56135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2946 (p : Pattern) (ha : d55744 p = 1) (hb : d56141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d55739 q = 1) (hb : d56136 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d55739, d56136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2945 q ha hb
    | true =>
      simp only [d55739, d56136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d55740 q = 1) (hb : d56137 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d55740, d56137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d55740, d56137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d55741 q = 1) (hb : d56138 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d55741, d56138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55741, d56138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d55742 q = 1) (hb : d56139 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d55742, d56139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d55742, d56139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d55743 q = 1) (hb : d56140 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d55743, d56140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d55743, d56140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d55744 q = 1) (hb : d56141 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d55744, d56141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55744, d56141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro2947 (p : Pattern) (ha : d48 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d47 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d48 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2948 (p : Pattern) (ha : d55 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d55 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2949 (p : Pattern) (ha : d2520 p = 1) (hb : d64793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2947 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2948 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d58 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d59 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2519 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2520 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro2950 (p : Pattern) (ha : d51643 p = 1) (hb : d56150 p = 1) : d3675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d120 q = 1) : d120 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51641 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51642 q = 1) (hb : d56150 q = 1) : d3674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d56150, d3674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51642, d56150, d3674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d51643 q = 1) (hb : d56150 q = 1) : d3675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d3675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d3675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2951 (p : Pattern) (ha : d51646 p = 1) (hb : d56150 p = 1) : d3677 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d120 q = 1) : d120 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51641 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51642 q = 1) (hb : d56150 q = 1) : d3674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d56150, d3674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51642, d56150, d3674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d198 q = 1) : d198 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51644 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51645 q = 1) (hb : d56150 q = 1) : d3676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d56150, d3676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51645, d56150, d3676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51646 q = 1) (hb : d56150 q = 1) : d3677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d3677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51646, d3677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2952 (p : Pattern) (ha : d56024 p = 1) (hb : d64793 p = 1) : d3683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1018 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3016 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3016, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3016, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51647 q = 1) (hb : d56150 q = 1) : d3678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d3678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2950 q ha hb
    | true =>
      simp only [d51647, d3678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2951 q ha hb
  have h6 (q : Pattern) (ha : d214 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2849 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51648 q = 1) (hb : d56150 q = 1) : d3679 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d3679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51648, d3679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51649 q = 1) (hb : d64793 q = 1) : d3680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d64793, d3680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51649, d64793, d3680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56022 q = 1) (hb : d64793 q = 1) : d3681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56022, d3681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56022, d3681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2525 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2849 q ha hb
  have h11 (q : Pattern) (ha : d2526 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2527 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2527, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2528 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56023 q = 1) (hb : d64793 q = 1) : d3682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56023, d3682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56023, d3682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56024 q = 1) (hb : d64793 q = 1) : d3683 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56024, d3683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56024, d3683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro2953 (p : Pattern) (ha : d397 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d283 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d102 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d103 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d397 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2954 (p : Pattern) (ha : d51660 p = 1) (hb : d56150 p = 1) : d3690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d300 q = 1) : d300 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51659 q = 1) (hb : d56150 q = 1) : d3689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d56150, d3689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51659, d56150, d3689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d51660 q = 1) (hb : d56150 q = 1) : d3690 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d3690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d3690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2955 (p : Pattern) (ha : d51663 p = 1) (hb : d56150 p = 1) : d3692 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d300 q = 1) : d300 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51659 q = 1) (hb : d56150 q = 1) : d3689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d56150, d3689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51659, d56150, d3689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d380 q = 1) : d380 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51661 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51662 q = 1) (hb : d56150 q = 1) : d3691 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51662, d56150, d3691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51662, d56150, d3691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51663 q = 1) (hb : d56150 q = 1) : d3692 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51663, d3692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51663, d3692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2956 (p : Pattern) (ha : d56032 p = 1) (hb : d64793 p = 1) : d3698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1021 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3025 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3025, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3025, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51664 q = 1) (hb : d56150 q = 1) : d3693 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d3693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2954 q ha hb
    | true =>
      simp only [d51664, d3693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2955 q ha hb
  have h6 (q : Pattern) (ha : d398 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2953 q ha hb
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1019 q ha hb
  have h7 (q : Pattern) (ha : d51665 q = 1) (hb : d56150 q = 1) : d3694 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d3694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51665, d3694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51666 q = 1) (hb : d64793 q = 1) : d3695 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d64793, d3695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51666, d64793, d3695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56030 q = 1) (hb : d64793 q = 1) : d3696 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56030, d3696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56030, d3696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2537 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2851 q ha hb
  have h11 (q : Pattern) (ha : d2538 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2539 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2539, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2540 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56031 q = 1) (hb : d64793 q = 1) : d3697 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56031, d3697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56031, d3697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56032 q = 1) (hb : d64793 q = 1) : d3698 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56032, d3698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56032, d3698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro2957 (p : Pattern) (ha : d56038 p = 1) (hb : d64793 p = 1) : d3704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2521 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2949 q ha hb
  have h2 (q : Pattern) (ha : d2522 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2523 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2524 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56025 q = 1) (hb : d64793 q = 1) : d3684 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56025, d3684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56025, d3684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2952 q ha hb
  have h6 (q : Pattern) (ha : d56026 q = 1) (hb : d64793 q = 1) : d3685 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56026, d3685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56026, d3685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d56027 q = 1) (hb : d64793 q = 1) : d3686 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56027, d3686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56027, d3686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d56028 q = 1) (hb : d64793 q = 1) : d3687 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56028, d3687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56028, d3687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d56029 q = 1) (hb : d64793 q = 1) : d3688 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56029, d3688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56029, d3688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d56033 q = 1) (hb : d64793 q = 1) : d3699 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56033, d3699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56033, d3699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2956 q ha hb
  have h11 (q : Pattern) (ha : d56034 q = 1) (hb : d64793 q = 1) : d3700 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56034, d3700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56034, d3700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d56035 q = 1) (hb : d64793 q = 1) : d3701 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56035, d3701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56035, d3701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d56036 q = 1) (hb : d64793 q = 1) : d3702 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56036, d3702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56036, d3702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d56037 q = 1) (hb : d64793 q = 1) : d3703 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56037, d3703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56037, d3703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56038 q = 1) (hb : d64793 q = 1) : d3704 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56038, d3704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56038, d3704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro2958 (p : Pattern) (ha : d638 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d496 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d636 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d637 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d638 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2959 (p : Pattern) (ha : d644 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d636 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d637 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d642 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d643 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d644 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2960 (p : Pattern) (ha : d51685 p = 1) (hb : d56150 p = 1) : d3706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d518 q = 1) : d518 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51684 q = 1) (hb : d56150 q = 1) : d3705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d56150, d3705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51684, d56150, d3705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d51685 q = 1) (hb : d56150 q = 1) : d3706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d3706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d3706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2961 (p : Pattern) (ha : d51688 p = 1) (hb : d56150 p = 1) : d3708 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d518 q = 1) : d518 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51683 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51684 q = 1) (hb : d56150 q = 1) : d3705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d56150, d3705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51684, d56150, d3705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d614 q = 1) : d614 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51687 q = 1) (hb : d56150 q = 1) : d3707 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51687, d56150, d3707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51687, d56150, d3707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51688 q = 1) (hb : d56150 q = 1) : d3708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51688, d3708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51688, d3708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2962 (p : Pattern) (ha : d56041 p = 1) (hb : d64793 p = 1) : d3714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1025 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3035 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3035, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3035, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51689 q = 1) (hb : d56150 q = 1) : d3709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d3709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2960 q ha hb
    | true =>
      simp only [d51689, d3709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2961 q ha hb
  have h6 (q : Pattern) (ha : d645 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2958 q ha hb
    | true =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2959 q ha hb
  have h7 (q : Pattern) (ha : d51690 q = 1) (hb : d56150 q = 1) : d3710 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d3710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51690, d3710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51691 q = 1) (hb : d64793 q = 1) : d3711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d64793, d3711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51691, d64793, d3711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56039 q = 1) (hb : d64793 q = 1) : d3712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56039, d3712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56039, d3712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2550 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2854 q ha hb
  have h11 (q : Pattern) (ha : d2551 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2552 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2552, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2553 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56040 q = 1) (hb : d64793 q = 1) : d3713 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56040, d3713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56040, d3713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56041 q = 1) (hb : d64793 q = 1) : d3714 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56041, d3714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56041, d3714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro2963 (p : Pattern) (ha : d56047 p = 1) (hb : d64793 p = 1) : d3720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56042 q = 1) (hb : d64793 q = 1) : d3715 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56042, d3715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56042, d3715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2962 q ha hb
  have h2 (q : Pattern) (ha : d56043 q = 1) (hb : d64793 q = 1) : d3716 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56043, d3716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56043, d3716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56044 q = 1) (hb : d64793 q = 1) : d3717 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56044, d3717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56044, d3717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56045 q = 1) (hb : d64793 q = 1) : d3718 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56045, d3718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56045, d3718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56046 q = 1) (hb : d64793 q = 1) : d3719 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56046, d3719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56046, d3719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56047 q = 1) (hb : d64793 q = 1) : d3720 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56047, d3720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56047, d3720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2964 (p : Pattern) (ha : d944 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d788 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d942 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d943 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d944 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2965 (p : Pattern) (ha : d950 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d942 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d943 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d948 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d949 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d950 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2966 (p : Pattern) (ha : d51711 p = 1) (hb : d56150 p = 1) : d3723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d810 q = 1) : d810 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51710 q = 1) (hb : d56150 q = 1) : d3722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d56150, d3722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51710, d56150, d3722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d51711 q = 1) (hb : d56150 q = 1) : d3723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d3723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d3723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2967 (p : Pattern) (ha : d51714 p = 1) (hb : d56150 p = 1) : d3725 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d810 q = 1) : d810 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51709 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51710 q = 1) (hb : d56150 q = 1) : d3722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d56150, d3722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51710, d56150, d3722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d920 q = 1) : d920 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51713 q = 1) (hb : d56150 q = 1) : d3724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51713, d56150, d3724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51713, d56150, d3724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51714 q = 1) (hb : d56150 q = 1) : d3725 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51714, d3725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51714, d3725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2968 (p : Pattern) (ha : d56051 p = 1) (hb : d64793 p = 1) : d3731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1029 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3046 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3046, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3046, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51715 q = 1) (hb : d56150 q = 1) : d3726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d3726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2966 q ha hb
    | true =>
      simp only [d51715, d3726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2967 q ha hb
  have h6 (q : Pattern) (ha : d951 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2964 q ha hb
    | true =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2965 q ha hb
  have h7 (q : Pattern) (ha : d51716 q = 1) (hb : d56150 q = 1) : d3727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d3727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51716, d3727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51717 q = 1) (hb : d64793 q = 1) : d3728 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d64793, d3728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51717, d64793, d3728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56049 q = 1) (hb : d64793 q = 1) : d3729 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56049, d3729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56049, d3729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2564 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2857 q ha hb
  have h11 (q : Pattern) (ha : d2565 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2566 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2566, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2567 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56050 q = 1) (hb : d64793 q = 1) : d3730 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56050, d3730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56050, d3730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56051 q = 1) (hb : d64793 q = 1) : d3731 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56051, d3731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56051, d3731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro2969 (p : Pattern) (ha : d56057 p = 1) (hb : d64793 p = 1) : d3737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56052 q = 1) (hb : d64793 q = 1) : d3732 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56052, d3732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56052, d3732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2968 q ha hb
  have h2 (q : Pattern) (ha : d56053 q = 1) (hb : d64793 q = 1) : d3733 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56053, d3733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56053, d3733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56054 q = 1) (hb : d64793 q = 1) : d3734 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56054, d3734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56054, d3734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56055 q = 1) (hb : d64793 q = 1) : d3735 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56055, d3735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56055, d3735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56056 q = 1) (hb : d64793 q = 1) : d3736 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56056, d3736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56056, d3736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56057 q = 1) (hb : d64793 q = 1) : d3737 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56057, d3737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56057, d3737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2970 (p : Pattern) (ha : d1355 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1166 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1167 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1353 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1354 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1355 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2971 (p : Pattern) (ha : d1361 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1353 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1354 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1359 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1360 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1361 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2972 (p : Pattern) (ha : d51738 p = 1) (hb : d56150 p = 1) : d3741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1189 q = 1) : d1189 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51736 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51737 q = 1) (hb : d56150 q = 1) : d3740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d56150, d3740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51737, d56150, d3740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d51738 q = 1) (hb : d56150 q = 1) : d3741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d3741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d3741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2973 (p : Pattern) (ha : d51741 p = 1) (hb : d56150 p = 1) : d3743 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1189 q = 1) : d1189 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51736 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51737 q = 1) (hb : d56150 q = 1) : d3740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d56150, d3740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51737, d56150, d3740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1331 q = 1) : d1331 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51739 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51740 q = 1) (hb : d56150 q = 1) : d3742 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d56150, d3742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51740, d56150, d3742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51741 q = 1) (hb : d56150 q = 1) : d3743 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d3743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51741, d3743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2974 (p : Pattern) (ha : d56062 p = 1) (hb : d64793 p = 1) : d3749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1033 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3058 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3058, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3058, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51742 q = 1) (hb : d56150 q = 1) : d3744 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d3744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2972 q ha hb
    | true =>
      simp only [d51742, d3744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2973 q ha hb
  have h6 (q : Pattern) (ha : d1362 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2970 q ha hb
    | true =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2971 q ha hb
  have h7 (q : Pattern) (ha : d51743 q = 1) (hb : d56150 q = 1) : d3745 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d3745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51743, d3745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51744 q = 1) (hb : d64793 q = 1) : d3746 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d64793, d3746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51744, d64793, d3746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56060 q = 1) (hb : d64793 q = 1) : d3747 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56060, d3747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56060, d3747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2579 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2860 q ha hb
  have h11 (q : Pattern) (ha : d2580 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2581 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2581, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2582 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56061 q = 1) (hb : d64793 q = 1) : d3748 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56061, d3748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56061, d3748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56062 q = 1) (hb : d64793 q = 1) : d3749 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56062, d3749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56062, d3749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro2975 (p : Pattern) (ha : d56068 p = 1) (hb : d64793 p = 1) : d3755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56063 q = 1) (hb : d64793 q = 1) : d3750 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56063, d3750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56063, d3750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2974 q ha hb
  have h2 (q : Pattern) (ha : d56064 q = 1) (hb : d64793 q = 1) : d3751 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56064, d3751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56064, d3751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56065 q = 1) (hb : d64793 q = 1) : d3752 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56065, d3752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56065, d3752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56066 q = 1) (hb : d64793 q = 1) : d3753 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56066, d3753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56066, d3753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56067 q = 1) (hb : d64793 q = 1) : d3754 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56067, d3754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56067, d3754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56068 q = 1) (hb : d64793 q = 1) : d3755 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56068, d3755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56068, d3755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2976 (p : Pattern) (ha : d1832 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1627 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1628 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1830 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1831 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1832 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2977 (p : Pattern) (ha : d1838 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1830 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1831 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1836 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1837 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1838 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2978 (p : Pattern) (ha : d51766 p = 1) (hb : d56150 p = 1) : d3760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1650 q = 1) : d1650 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51765 q = 1) (hb : d56150 q = 1) : d3759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d56150, d3759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51765, d56150, d3759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d51766 q = 1) (hb : d56150 q = 1) : d3760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d3760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d3760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2979 (p : Pattern) (ha : d51769 p = 1) (hb : d56150 p = 1) : d3762 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1650 q = 1) : d1650 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51765 q = 1) (hb : d56150 q = 1) : d3759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d56150, d3759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51765, d56150, d3759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d1808 q = 1) : d1808 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51767 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51768 q = 1) (hb : d56150 q = 1) : d3761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d56150, d3761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51768, d56150, d3761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51769 q = 1) (hb : d56150 q = 1) : d3762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d3762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51769, d3762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2980 (p : Pattern) (ha : d56074 p = 1) (hb : d64793 p = 1) : d3768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1037 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3071 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3071, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3071, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51770 q = 1) (hb : d56150 q = 1) : d3763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d3763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2978 q ha hb
    | true =>
      simp only [d51770, d3763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2979 q ha hb
  have h6 (q : Pattern) (ha : d1839 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2976 q ha hb
    | true =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2977 q ha hb
  have h7 (q : Pattern) (ha : d51771 q = 1) (hb : d56150 q = 1) : d3764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d3764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51771, d3764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51772 q = 1) (hb : d64793 q = 1) : d3765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d64793, d3765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51772, d64793, d3765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56072 q = 1) (hb : d64793 q = 1) : d3766 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56072, d3766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56072, d3766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2595 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2863 q ha hb
  have h11 (q : Pattern) (ha : d2596 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2597 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2597, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2598 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56073 q = 1) (hb : d64793 q = 1) : d3767 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56073, d3767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56073, d3767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56074 q = 1) (hb : d64793 q = 1) : d3768 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56074, d3768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56074, d3768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro2981 (p : Pattern) (ha : d56080 p = 1) (hb : d64793 p = 1) : d3774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56075 q = 1) (hb : d64793 q = 1) : d3769 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56075, d3769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56075, d3769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2980 q ha hb
  have h2 (q : Pattern) (ha : d56076 q = 1) (hb : d64793 q = 1) : d3770 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56076, d3770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56076, d3770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56077 q = 1) (hb : d64793 q = 1) : d3771 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56077, d3771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56077, d3771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56078 q = 1) (hb : d64793 q = 1) : d3772 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56078, d3772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56078, d3772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56079 q = 1) (hb : d64793 q = 1) : d3773 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56079, d3773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56079, d3773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56080 q = 1) (hb : d64793 q = 1) : d3774 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56080, d3774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56080, d3774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2982 (p : Pattern) (ha : d2310 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2111 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2309 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2310 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2983 (p : Pattern) (ha : d2316 p = 1) (hb : d56150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2309 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2314 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2315 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d56150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d2316 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro2984 (p : Pattern) (ha : d51795 p = 1) (hb : d56150 p = 1) : d3780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2133 q = 1) : d2133 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51794 q = 1) (hb : d56150 q = 1) : d3779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d56150, d3779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d51794, d56150, d3779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d51795 q = 1) (hb : d56150 q = 1) : d3780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d3780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d3780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro2985 (p : Pattern) (ha : d51798 p = 1) (hb : d56150 p = 1) : d3782 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d2133 q = 1) : d2133 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51794 q = 1) (hb : d56150 q = 1) : d3779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d56150, d3779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51794, d56150, d3779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d2286 q = 1) : d2286 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51796 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51797 q = 1) (hb : d56150 q = 1) : d3781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d56150, d3781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51797, d56150, d3781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51798 q = 1) (hb : d56150 q = 1) : d3782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d3782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51798, d3782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2986 (p : Pattern) (ha : d56087 p = 1) (hb : d64793 p = 1) : d3788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1041 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3085 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3085, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3085, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51799 q = 1) (hb : d56150 q = 1) : d3783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d3783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2984 q ha hb
    | true =>
      simp only [d51799, d3783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2985 q ha hb
  have h6 (q : Pattern) (ha : d2317 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2982 q ha hb
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2983 q ha hb
  have h7 (q : Pattern) (ha : d51800 q = 1) (hb : d56150 q = 1) : d3784 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d3784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51800, d3784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51801 q = 1) (hb : d64793 q = 1) : d3785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d64793, d3785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51801, d64793, d3785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d56085 q = 1) (hb : d64793 q = 1) : d3786 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d56085, d3786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56085, d3786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2612 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2866 q ha hb
  have h11 (q : Pattern) (ha : d2613 q = 1) (hb : d56150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2614 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2614, d64793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2615 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d2615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56086 q = 1) (hb : d64793 q = 1) : d3787 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d56086, d3787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d56086, d3787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56087 q = 1) (hb : d64793 q = 1) : d3788 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d56087, d3788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56087, d3788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h16 p ha hb
theorem andIntro2987 (p : Pattern) (ha : d56093 p = 1) (hb : d64793 p = 1) : d3794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56088 q = 1) (hb : d64793 q = 1) : d3789 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d56088, d3789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56088, d3789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2986 q ha hb
  have h2 (q : Pattern) (ha : d56089 q = 1) (hb : d64793 q = 1) : d3790 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d56089, d3790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56089, d3790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d56090 q = 1) (hb : d64793 q = 1) : d3791 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d56090, d3791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56090, d3791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56091 q = 1) (hb : d64793 q = 1) : d3792 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d56091, d3792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56091, d3792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d56092 q = 1) (hb : d64793 q = 1) : d3793 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d56092, d3793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56092, d3793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56093 q = 1) (hb : d64793 q = 1) : d3794 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d56093, d3794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56093, d3794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2988 (p : Pattern) (ha : d56099 p = 1) (hb : d64793 p = 1) : d3800 p = 1 := by
  have h0 (q : Pattern) (ha : d56048 q = 1) (hb : d64793 q = 1) : d3721 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56048, d3721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2957 q ha hb
    | true =>
      simp only [d56048, d3721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2963 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d56058 q = 1) (hb : d64793 q = 1) : d3738 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56058, d3738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56058, d3738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2969 q ha hb
  have h3 (q : Pattern) (ha : d56059 q = 1) (hb : d64793 q = 1) : d3739 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56059, d3739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d56059, d3739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d56069 q = 1) (hb : d64793 q = 1) : d3756 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56069, d3756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56069, d3756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2975 q ha hb
  have h5 (q : Pattern) (ha : d56070 q = 1) (hb : d64793 q = 1) : d3757 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56070, d3757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56070, d3757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d56071 q = 1) (hb : d64793 q = 1) : d3758 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56071, d3758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56071, d3758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d56081 q = 1) (hb : d64793 q = 1) : d3775 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56081, d3775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56081, d3775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2981 q ha hb
  have h8 (q : Pattern) (ha : d56082 q = 1) (hb : d64793 q = 1) : d3776 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56082, d3776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56082, d3776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d56083 q = 1) (hb : d64793 q = 1) : d3777 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56083, d3777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56083, d3777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d56084 q = 1) (hb : d64793 q = 1) : d3778 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d56084, d3778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d56084, d3778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d56094 q = 1) (hb : d64793 q = 1) : d3795 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d56094, d3795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56094, d3795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2987 q ha hb
  have h12 (q : Pattern) (ha : d56095 q = 1) (hb : d64793 q = 1) : d3796 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d56095, d3796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56095, d3796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d56096 q = 1) (hb : d64793 q = 1) : d3797 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d56096, d3797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56096, d3797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d56097 q = 1) (hb : d64793 q = 1) : d3798 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d56097, d3798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56097, d3798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d56098 q = 1) (hb : d64793 q = 1) : d3799 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d56098, d3799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d56098, d3799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d56099 q = 1) (hb : d64793 q = 1) : d3800 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d56099, d3800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d56099, d3800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro2989 (p : Pattern) (ha : d56105 p = 1) (hb : d64793 p = 1) : d3806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56100 q = 1) (hb : d64793 q = 1) : d3801 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d56100, d3801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2988 q ha hb
    | true =>
      simp only [d56100, d3801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56101 q = 1) (hb : d64793 q = 1) : d3802 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d56101, d3802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56101, d3802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56102 q = 1) (hb : d64793 q = 1) : d3803 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d56102, d3803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56102, d3803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56103 q = 1) (hb : d64793 q = 1) : d3804 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d56103, d3804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56103, d3804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56104 q = 1) (hb : d64793 q = 1) : d3805 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d56104, d3805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56104, d3805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56105 q = 1) (hb : d64793 q = 1) : d3806 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d56105, d3806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56105, d3806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2990 (p : Pattern) (ha : d56111 p = 1) (hb : d64793 p = 1) : d3812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56106 q = 1) (hb : d64793 q = 1) : d3807 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d56106, d3807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2989 q ha hb
    | true =>
      simp only [d56106, d3807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56107 q = 1) (hb : d64793 q = 1) : d3808 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d56107, d3808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56107, d3808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56108 q = 1) (hb : d64793 q = 1) : d3809 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d56108, d3809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56108, d3809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56109 q = 1) (hb : d64793 q = 1) : d3810 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d56109, d3810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56109, d3810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56110 q = 1) (hb : d64793 q = 1) : d3811 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d56110, d3811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56110, d3811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56111 q = 1) (hb : d64793 q = 1) : d3812 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d56111, d3812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56111, d3812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2991 (p : Pattern) (ha : d56117 p = 1) (hb : d64793 p = 1) : d3818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56112 q = 1) (hb : d64793 q = 1) : d3813 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d56112, d3813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2990 q ha hb
    | true =>
      simp only [d56112, d3813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56113 q = 1) (hb : d64793 q = 1) : d3814 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d56113, d3814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56113, d3814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56114 q = 1) (hb : d64793 q = 1) : d3815 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d56114, d3815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56114, d3815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56115 q = 1) (hb : d64793 q = 1) : d3816 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d56115, d3816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56115, d3816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56116 q = 1) (hb : d64793 q = 1) : d3817 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d56116, d3817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56116, d3817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56117 q = 1) (hb : d64793 q = 1) : d3818 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d56117, d3818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56117, d3818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2992 (p : Pattern) (ha : d56123 p = 1) (hb : d64793 p = 1) : d3824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56118 q = 1) (hb : d64793 q = 1) : d3819 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d56118, d3819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2991 q ha hb
    | true =>
      simp only [d56118, d3819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56119 q = 1) (hb : d64793 q = 1) : d3820 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d56119, d3820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56119, d3820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56120 q = 1) (hb : d64793 q = 1) : d3821 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d56120, d3821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56120, d3821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56121 q = 1) (hb : d64793 q = 1) : d3822 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d56121, d3822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56121, d3822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56122 q = 1) (hb : d64793 q = 1) : d3823 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d56122, d3823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56122, d3823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56123 q = 1) (hb : d64793 q = 1) : d3824 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d56123, d3824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56123, d3824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2993 (p : Pattern) (ha : d56129 p = 1) (hb : d64793 p = 1) : d3830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56124 q = 1) (hb : d64793 q = 1) : d3825 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d56124, d3825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2992 q ha hb
    | true =>
      simp only [d56124, d3825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56125 q = 1) (hb : d64793 q = 1) : d3826 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d56125, d3826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56125, d3826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56126 q = 1) (hb : d64793 q = 1) : d3827 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d56126, d3827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56126, d3827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56127 q = 1) (hb : d64793 q = 1) : d3828 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d56127, d3828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56127, d3828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56128 q = 1) (hb : d64793 q = 1) : d3829 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d56128, d3829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56128, d3829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56129 q = 1) (hb : d64793 q = 1) : d3830 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d56129, d3830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56129, d3830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2994 (p : Pattern) (ha : d56135 p = 1) (hb : d64793 p = 1) : d3836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56130 q = 1) (hb : d64793 q = 1) : d3831 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d56130, d3831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2993 q ha hb
    | true =>
      simp only [d56130, d3831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56131 q = 1) (hb : d64793 q = 1) : d3832 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d56131, d3832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56131, d3832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56132 q = 1) (hb : d64793 q = 1) : d3833 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d56132, d3833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56132, d3833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56133 q = 1) (hb : d64793 q = 1) : d3834 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d56133, d3834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56133, d3834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56134 q = 1) (hb : d64793 q = 1) : d3835 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d56134, d3835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56134, d3835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56135 q = 1) (hb : d64793 q = 1) : d3836 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d56135, d3836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56135, d3836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2995 (p : Pattern) (ha : d56141 p = 1) (hb : d64793 p = 1) : d3842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d64793 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56136 q = 1) (hb : d64793 q = 1) : d3837 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d56136, d3837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2994 q ha hb
    | true =>
      simp only [d56136, d3837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d56137 q = 1) (hb : d64793 q = 1) : d3838 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d56137, d3838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d56137, d3838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d56138 q = 1) (hb : d64793 q = 1) : d3839 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d56138, d3839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d56138, d3839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d56139 q = 1) (hb : d64793 q = 1) : d3840 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d56139, d3840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d56139, d3840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d56140 q = 1) (hb : d64793 q = 1) : d3841 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d56140, d3841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d56140, d3841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d56141 q = 1) (hb : d64793 q = 1) : d3842 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d56141, d3842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d56141, d3842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2996 (p : Pattern) (ha : d3675 p = 1) (hb : d64796 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d3674 q = 1) (hb : d64795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3674, d64795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3674, d64795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3675 q = 1) (hb : d64796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3675, d64796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3675, d64796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro2997 (p : Pattern) (ha : d3677 p = 1) (hb : d64798 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d3674 q = 1) (hb : d64795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3674, d64795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3674, d64795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3676 q = 1) (hb : d64797 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3676, d64797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d3676, d64797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d3677 q = 1) (hb : d64798 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3677, d64798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3677, d64798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro2998 (p : Pattern) (ha : d3683 p = 1) (hb : d64804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3678 q = 1) (hb : d64799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3678, d64799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2996 q ha hb
    | true =>
      simp only [d3678, d64799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2997 q ha hb
  have h2 (q : Pattern) (ha : d3679 q = 1) (hb : d64800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3679, d64800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3679, d64800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3680 q = 1) (hb : d64801 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3680, d64801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3680, d64801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3681 q = 1) (hb : d64802 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3681, d64802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3681, d64802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3682 q = 1) (hb : d64803 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3682, d64803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3682, d64803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3683 q = 1) (hb : d64804 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3683, d64804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3683, d64804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro2999 (p : Pattern) (ha : d3690 p = 1) (hb : d64811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51 q ha hb
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3689 q = 1) (hb : d64810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3689, d64810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3689, d64810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3690 q = 1) (hb : d64811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3690, d64811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3690, d64811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
