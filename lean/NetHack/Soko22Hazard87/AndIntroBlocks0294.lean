import NetHack.Soko22Hazard87.AndIntroBlocks0293
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro73500 (p : Pattern) (ha : d266246 p = 1) (hb : d279932 p = 1) : d267792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266246 q = 1) (hb : d279927 q = 1) : d267787 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d279927, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73499 q ha hb
    | true =>
      simp only [d279927, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d266246 q = 1) (hb : d279928 q = 1) : d267788 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d279928, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279928, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d266246 q = 1) (hb : d279929 q = 1) : d267789 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d279929, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279929, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d266246 q = 1) (hb : d279930 q = 1) : d267790 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d279930, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279930, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d266246 q = 1) (hb : d279931 q = 1) : d267791 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d279931, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279931, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d266246 q = 1) (hb : d279932 q = 1) : d267792 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d279932, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279932, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73501 (p : Pattern) (ha : d266246 p = 1) (hb : d279938 p = 1) : d267798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266246 q = 1) (hb : d279933 q = 1) : d267793 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d279933, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73500 q ha hb
    | true =>
      simp only [d279933, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d266246 q = 1) (hb : d279934 q = 1) : d267794 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d279934, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279934, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d266246 q = 1) (hb : d279935 q = 1) : d267795 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d279935, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279935, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d266246 q = 1) (hb : d279936 q = 1) : d267796 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d279936, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279936, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d266246 q = 1) (hb : d279937 q = 1) : d267797 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d279937, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279937, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d266246 q = 1) (hb : d279938 q = 1) : d267798 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d279938, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279938, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73502 (p : Pattern) (ha : d266246 p = 1) (hb : d279944 p = 1) : d267804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266246 q = 1) (hb : d279939 q = 1) : d267799 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d279939, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73501 q ha hb
    | true =>
      simp only [d279939, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d266246 q = 1) (hb : d279940 q = 1) : d267800 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d279940, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279940, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d266246 q = 1) (hb : d279941 q = 1) : d267801 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d279941, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279941, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d266246 q = 1) (hb : d279942 q = 1) : d267802 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d279942, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279942, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d266246 q = 1) (hb : d279943 q = 1) : d267803 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d279943, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279943, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d266246 q = 1) (hb : d279944 q = 1) : d267804 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d279944, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279944, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73503 (p : Pattern) (ha : d266246 p = 1) (hb : d279950 p = 1) : d267810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266246 q = 1) (hb : d279945 q = 1) : d267805 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d279945, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73502 q ha hb
    | true =>
      simp only [d279945, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d266246 q = 1) (hb : d279946 q = 1) : d267806 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d279946, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279946, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d266246 q = 1) (hb : d279947 q = 1) : d267807 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d279947, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279947, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d266246 q = 1) (hb : d279948 q = 1) : d267808 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d279948, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279948, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d266246 q = 1) (hb : d279949 q = 1) : d267809 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d279949, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279949, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d266246 q = 1) (hb : d279950 q = 1) : d267810 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d279950, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279950, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73504 (p : Pattern) (ha : d25187 p = 1) (hb : d198617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198569 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198575 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198606 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25123 q = 1) (hb : d198489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73157 q ha hb
    | true =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d25183 q = 1) (hb : d198607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d198607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25183, d198607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d198613 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25184 q = 1) (hb : d198614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d198614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25184, d198614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25185 q = 1) (hb : d198615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d198615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25185, d198615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25186 q = 1) (hb : d198616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d198616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25186, d198616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25187 q = 1) (hb : d198617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d198617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d198617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73505 (p : Pattern) (ha : d25194 p = 1) (hb : d198636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198569 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198606 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25123 q = 1) (hb : d198489 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73157 q ha hb
    | true =>
      simp only [d25123, d198489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d25183 q = 1) (hb : d198607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d198607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25183, d198607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d198613 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25184 q = 1) (hb : d198614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d198614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25184, d198614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25185 q = 1) (hb : d198615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d198615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25185, d198615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25186 q = 1) (hb : d198616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d198616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d198616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198622 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d198626 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d198628 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25130 q = 1) (hb : d198496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73159 q ha hb
    | true =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d25190 q = 1) (hb : d198629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d198629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25190, d198629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198632 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25191 q = 1) (hb : d198633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d198633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25191, d198633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25192 q = 1) (hb : d198634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d198634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25192, d198634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25193 q = 1) (hb : d198635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d198635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25193, d198635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d25194 q = 1) (hb : d198636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d198636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25194, d198636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73506 (p : Pattern) (ha : d198645 p = 1) (hb : d245682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25130 q = 1) (hb : d198496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73159 q ha hb
    | true =>
      simp only [d25130, d198496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d25190 q = 1) (hb : d198629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d198629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25190, d198629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198632 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25191 q = 1) (hb : d198633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d198633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25191, d198633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25192 q = 1) (hb : d198643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d198643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d198643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25193 q = 1) (hb : d198644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d198644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d198644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198645 q = 1) (hb : d245682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198645, d245682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198645, d245682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro73507 (p : Pattern) (ha : d198685 p = 1) (hb : d245692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198674 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25166 q = 1) (hb : d198532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d198532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73164 q ha hb
    | true =>
      simp only [d25166, d198532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d198675 q = 1) (hb : d245688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198675, d245688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198675, d245688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198681 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198682 q = 1) (hb : d245689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198682, d245689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198682, d245689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198683 q = 1) (hb : d245690 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198683, d245690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198683, d245690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198684 q = 1) (hb : d245691 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198684, d245691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198684, d245691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198685 q = 1) (hb : d245692 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198685, d245692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198685, d245692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73508 (p : Pattern) (ha : d198691 p = 1) (hb : d245698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d198637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d198637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73504 q ha hb
    | true =>
      simp only [d25195, d198637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73505 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25196 q = 1) (hb : d198640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d198640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d198640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198641 q = 1) (hb : d245680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198641, d245680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d198641, d245680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198642 q = 1) (hb : d245681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198642, d245681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198642, d245681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198646 q = 1) (hb : d245683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198646, d245683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198646, d245683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73506 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d198647 q = 1) (hb : d245684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198647, d245684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d198647, d245684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198648 q = 1) (hb : d245685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198648, d245685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d198648, d245685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198649 q = 1) (hb : d245686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198649, d245686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d198649, d245686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d198650 q = 1) (hb : d245687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198650, d245687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d198650, d245687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198686 q = 1) (hb : d245693 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198686, d245693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198686, d245693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73507 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198687 q = 1) (hb : d245694 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198687, d245694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198687, d245694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198688 q = 1) (hb : d245695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198688, d245695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d198688, d245695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198689 q = 1) (hb : d245696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198689, d245696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d198689, d245696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d198690 q = 1) (hb : d245697 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198690, d245697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d198690, d245697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d198691 q = 1) (hb : d245698 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d198691, d245698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d198691, d245698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73509 (p : Pattern) (ha : d198697 p = 1) (hb : d245704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d198544 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d198544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d198544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47793 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d198545 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d198545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d198545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d198546 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d198546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d198546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d198547 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d198547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d198547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d198548 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d198548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d198548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198692 q = 1) (hb : d245699 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d198692, d245699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198692, d245699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73508 q ha hb
  have h8 (q : Pattern) (ha : d198693 q = 1) (hb : d245700 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d198693, d245700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198693, d245700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198694 q = 1) (hb : d245701 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d198694, d245701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198694, d245701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198695 q = 1) (hb : d245702 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d198695, d245702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198695, d245702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d198696 q = 1) (hb : d245703 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d198696, d245703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198696, d245703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d198697 q = 1) (hb : d245704 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d198697, d245704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d198697, d245704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro73510 (p : Pattern) (ha : d198808 p = 1) (hb : d266340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d198797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198715 q = 1) (hb : d266335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198715, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73200 q ha hb
    | true =>
      simp only [d198715, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73192 q hb ha
  have h5 (q : Pattern) (ha : d198798 q = 1) (hb : d266336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198798, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d198798, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d198804 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d198805 q = 1) (hb : d266337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198805, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d198805, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d198806 q = 1) (hb : d266338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198806, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198806, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198807 q = 1) (hb : d266339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198807, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198807, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198808 q = 1) (hb : d266340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198808, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198808, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73511 (p : Pattern) (ha : d198829 p = 1) (hb : d266349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198715 q = 1) (hb : d266335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198715, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73200 q ha hb
    | true =>
      simp only [d198715, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73192 q hb ha
  have h4 (q : Pattern) (ha : d198798 q = 1) (hb : d266336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198798, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d198798, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d198804 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d198805 q = 1) (hb : d266337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198805, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d198805, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d198806 q = 1) (hb : d266338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198806, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198806, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198807 q = 1) (hb : d266339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198807, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198807, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198814 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d198819 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d198821 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198725 q = 1) (hb : d266344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198725, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73202 q ha hb
    | true =>
      simp only [d198725, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73193 q hb ha
  have h13 (q : Pattern) (ha : d198822 q = 1) (hb : d266345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198822, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d198822, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198825 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198826 q = 1) (hb : d266346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198826, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198826, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198827 q = 1) (hb : d266347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198827, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d198827, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d198828 q = 1) (hb : d266348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198828, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d198828, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d198829 q = 1) (hb : d266349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198829, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d198829, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73512 (p : Pattern) (ha : d198849 p = 1) (hb : d267625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198821 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198725 q = 1) (hb : d266344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198725, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73202 q ha hb
    | true =>
      simp only [d198725, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73193 q hb ha
  have h3 (q : Pattern) (ha : d198822 q = 1) (hb : d266345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198822, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198822, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198825 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198826 q = 1) (hb : d266346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198826, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198826, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198847 q = 1) (hb : d266347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198847, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198847, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198848 q = 1) (hb : d266348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198848, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198848, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198849 q = 1) (hb : d267625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198849, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198849, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73513 (p : Pattern) (ha : d198917 p = 1) (hb : d267636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198901 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198906 q = 1) (hb : d267631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198906, d267631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73229 q ha hb
    | true =>
      simp only [d198906, d267631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73197 q hb ha
  have h3 (q : Pattern) (ha : d198907 q = 1) (hb : d267632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d198907, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d198907, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d198913 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198914 q = 1) (hb : d267633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d198914, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198914, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198915 q = 1) (hb : d267634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198915, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198915, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198916 q = 1) (hb : d267635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d198916, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198916, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d198917 q = 1) (hb : d267636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d198917, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198917, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73514 (p : Pattern) (ha : d198930 p = 1) (hb : d267642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198830 q = 1) (hb : d266350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198830, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73510 q ha hb
    | true =>
      simp only [d198830, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73511 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d198843 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198844 q = 1) (hb : d266351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198844, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d198844, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d198845 q = 1) (hb : d267623 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198845, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d198845, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d198846 q = 1) (hb : d267624 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198846, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198846, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198850 q = 1) (hb : d267626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198850, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198850, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73512 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d198852 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d198853 q = 1) (hb : d267627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198853, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d198853, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d198854 q = 1) (hb : d267628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198854, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d198854, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d198855 q = 1) (hb : d267629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198855, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d198855, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d198856 q = 1) (hb : d267630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198856, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d198856, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198918 q = 1) (hb : d267637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d198918, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d198918, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73513 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d198925 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d198926 q = 1) (hb : d267638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d198926, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d198926, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d198927 q = 1) (hb : d267639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d198927, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d198927, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d198928 q = 1) (hb : d267640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d198928, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d198928, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d198929 q = 1) (hb : d267641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d198929, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d198929, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d198930 q = 1) (hb : d267642 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d198930, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d198930, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73515 (p : Pattern) (ha : d198936 p = 1) (hb : d267648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198931 q = 1) (hb : d267643 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d198931, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198931, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73514 q ha hb
  have h2 (q : Pattern) (ha : d198932 q = 1) (hb : d267644 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d198932, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198932, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198933 q = 1) (hb : d267645 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d198933, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198933, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198934 q = 1) (hb : d267646 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d198934, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198934, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198935 q = 1) (hb : d267647 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d198935, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198935, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198936 q = 1) (hb : d267648 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d198936, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d198936, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73516 (p : Pattern) (ha : d199065 p = 1) (hb : d266529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199054 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d198973 q = 1) (hb : d266524 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198973, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73238 q ha hb
    | true =>
      simp only [d198973, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73239 q ha hb
  have h5 (q : Pattern) (ha : d199055 q = 1) (hb : d266525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199055, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199055, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199061 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199062 q = 1) (hb : d266526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199062, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199062, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199063 q = 1) (hb : d266527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199063, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199063, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199064 q = 1) (hb : d266528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199064, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199064, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199065 q = 1) (hb : d266529 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199065, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199065, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73517 (p : Pattern) (ha : d199086 p = 1) (hb : d266539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198999 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d198973 q = 1) (hb : d266524 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198973, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73238 q ha hb
    | true =>
      simp only [d198973, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73239 q ha hb
  have h4 (q : Pattern) (ha : d199055 q = 1) (hb : d266525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199055, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199055, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199061 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199062 q = 1) (hb : d266526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199062, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199062, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199063 q = 1) (hb : d266527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199063, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199063, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199064 q = 1) (hb : d266528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199064, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199064, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199071 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199076 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199078 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d198983 q = 1) (hb : d266534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198983, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73241 q ha hb
    | true =>
      simp only [d198983, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73242 q ha hb
  have h13 (q : Pattern) (ha : d199079 q = 1) (hb : d266535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199079, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199079, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199082 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199083 q = 1) (hb : d266536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199083, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199083, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199084 q = 1) (hb : d266537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199084, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199084, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199085 q = 1) (hb : d266538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199085, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199085, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199086 q = 1) (hb : d266539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199086, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199086, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73518 (p : Pattern) (ha : d199106 p = 1) (hb : d267652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198983 q = 1) (hb : d266534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d198983, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73241 q ha hb
    | true =>
      simp only [d198983, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73242 q ha hb
  have h3 (q : Pattern) (ha : d199079 q = 1) (hb : d266535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199079, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199079, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199082 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199083 q = 1) (hb : d266536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199083, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199083, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199104 q = 1) (hb : d266537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199104, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199104, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199105 q = 1) (hb : d266538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199105, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199105, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199106 q = 1) (hb : d267652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199106, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199106, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73519 (p : Pattern) (ha : d199191 p = 1) (hb : d267663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199180 q = 1) (hb : d267658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199180, d267658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73276 q ha hb
    | true =>
      simp only [d199180, d267658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73279 q ha hb
  have h3 (q : Pattern) (ha : d199181 q = 1) (hb : d267659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199181, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199181, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199187 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199188 q = 1) (hb : d267660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199188, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199188, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199189 q = 1) (hb : d267661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199189, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199189, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199190 q = 1) (hb : d267662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199190, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199190, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199191 q = 1) (hb : d267663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199191, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199191, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73520 (p : Pattern) (ha : d199204 p = 1) (hb : d267669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198991 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199087 q = 1) (hb : d266540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199087, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73516 q ha hb
    | true =>
      simp only [d199087, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73517 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199101 q = 1) (hb : d266541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199101, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199101, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199102 q = 1) (hb : d267650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199102, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199102, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199103 q = 1) (hb : d267651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199103, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199103, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199107 q = 1) (hb : d267653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199107, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199107, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73518 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199109 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199110 q = 1) (hb : d267654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199110, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199110, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199111 q = 1) (hb : d267655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199111, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199111, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199112 q = 1) (hb : d267656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199112, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199112, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199113 q = 1) (hb : d267657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199113, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199113, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199192 q = 1) (hb : d267664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199192, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199192, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73519 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199199 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199200 q = 1) (hb : d267665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199200, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199200, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199201 q = 1) (hb : d267666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199201, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199201, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199202 q = 1) (hb : d267667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199202, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199202, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199203 q = 1) (hb : d267668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199203, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199203, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199204 q = 1) (hb : d267669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199204, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199204, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73521 (p : Pattern) (ha : d199210 p = 1) (hb : d267675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199205 q = 1) (hb : d267670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199205, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199205, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73520 q ha hb
  have h2 (q : Pattern) (ha : d199206 q = 1) (hb : d267671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199206, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199206, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199207 q = 1) (hb : d267672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199207, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199207, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199208 q = 1) (hb : d267673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199208, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199208, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199209 q = 1) (hb : d267674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199209, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199209, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199210 q = 1) (hb : d267675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199210, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199210, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73522 (p : Pattern) (ha : d199376 p = 1) (hb : d266774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199318 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199283 q = 1) (hb : d266769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199283, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73293 q ha hb
    | true =>
      simp only [d199283, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73294 q ha hb
  have h5 (q : Pattern) (ha : d199357 q = 1) (hb : d266770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199357, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199357, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199372 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199373 q = 1) (hb : d266771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199373, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199373, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199374 q = 1) (hb : d266772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199374, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199374, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199375 q = 1) (hb : d266773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199375, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199375, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199376 q = 1) (hb : d266774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199376, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199376, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73523 (p : Pattern) (ha : d199397 p = 1) (hb : d266784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199309 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199283 q = 1) (hb : d266769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199283, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73293 q ha hb
    | true =>
      simp only [d199283, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73294 q ha hb
  have h4 (q : Pattern) (ha : d199357 q = 1) (hb : d266770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199357, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199357, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199373 q = 1) (hb : d266771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199373, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199373, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199374 q = 1) (hb : d266772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199374, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199374, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199375 q = 1) (hb : d266773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199375, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199375, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199389 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199293 q = 1) (hb : d266779 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199293, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73296 q ha hb
    | true =>
      simp only [d199293, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73297 q ha hb
  have h13 (q : Pattern) (ha : d199390 q = 1) (hb : d266780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199390, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199390, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199394 q = 1) (hb : d266781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199394, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199394, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199395 q = 1) (hb : d266782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199395, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199395, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199396 q = 1) (hb : d266783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199396, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199396, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199397 q = 1) (hb : d266784 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199397, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199397, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73524 (p : Pattern) (ha : d199417 p = 1) (hb : d267680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199293 q = 1) (hb : d266779 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199293, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73296 q ha hb
    | true =>
      simp only [d199293, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73297 q ha hb
  have h3 (q : Pattern) (ha : d199390 q = 1) (hb : d266780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199390, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199390, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199394 q = 1) (hb : d266781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199394, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199394, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199415 q = 1) (hb : d266782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199415, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199415, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199416 q = 1) (hb : d266783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199416, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199416, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199417 q = 1) (hb : d267680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199417, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199417, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73525 (p : Pattern) (ha : d199528 p = 1) (hb : d267691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199508 q = 1) (hb : d267686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199508, d267686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73333 q ha hb
    | true =>
      simp only [d199508, d267686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73338 q ha hb
  have h3 (q : Pattern) (ha : d199509 q = 1) (hb : d267687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199509, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199509, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199524 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199525 q = 1) (hb : d267688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199525, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199525, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199526 q = 1) (hb : d267689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199526, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199526, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199527 q = 1) (hb : d267690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199527, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199527, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199528 q = 1) (hb : d267691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199528, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199528, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73526 (p : Pattern) (ha : d199541 p = 1) (hb : d267697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199301 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199398 q = 1) (hb : d266785 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199398, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73522 q ha hb
    | true =>
      simp only [d199398, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73523 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199412 q = 1) (hb : d266786 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199412, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199412, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199413 q = 1) (hb : d267678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199413, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199413, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199414 q = 1) (hb : d267679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199414, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199414, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199418 q = 1) (hb : d267681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199418, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199418, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73524 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199420 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199421 q = 1) (hb : d267682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199421, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199421, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199422 q = 1) (hb : d267683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199422, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199422, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199423 q = 1) (hb : d267684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199423, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199423, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199424 q = 1) (hb : d267685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199424, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199424, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199529 q = 1) (hb : d267692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199529, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199529, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73525 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199536 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199537 q = 1) (hb : d267693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199537, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199537, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199538 q = 1) (hb : d267694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199538, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199538, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199539 q = 1) (hb : d267695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199539, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199539, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199540 q = 1) (hb : d267696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199540, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199540, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199541 q = 1) (hb : d267697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199541, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199541, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73527 (p : Pattern) (ha : d199547 p = 1) (hb : d267703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199542 q = 1) (hb : d267698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199542, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199542, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73526 q ha hb
  have h2 (q : Pattern) (ha : d199543 q = 1) (hb : d267699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199543, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199543, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199544 q = 1) (hb : d267700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199544, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199544, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199545 q = 1) (hb : d267701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199545, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199545, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199546 q = 1) (hb : d267702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199546, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199546, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199547 q = 1) (hb : d267703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199547, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199547, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73528 (p : Pattern) (ha : d199712 p = 1) (hb : d267067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199643 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199652 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199682 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199617 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73353 q ha hb
    | true =>
      simp only [d199617, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73354 q ha hb
  have h5 (q : Pattern) (ha : d199683 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d199683, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d199708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d199709 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199709, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d199710 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199710, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199711 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199711, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199712 q = 1) (hb : d267067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199712, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199712, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73529 (p : Pattern) (ha : d199733 p = 1) (hb : d267077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199682 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199617 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199617, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73353 q ha hb
    | true =>
      simp only [d199617, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73354 q ha hb
  have h4 (q : Pattern) (ha : d199683 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199683, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d199683, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d199708 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199709 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199709, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199709, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d199710 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199710, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199710, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199711 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199711, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199711, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d199718 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d199723 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d199725 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199627 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73356 q ha hb
    | true =>
      simp only [d199627, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73357 q ha hb
  have h13 (q : Pattern) (ha : d199726 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d199726, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199729 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199730 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199730, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199731 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199731, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d199731, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d199732 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199732, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d199732, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d199733 q = 1) (hb : d267077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199733, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d199733, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73530 (p : Pattern) (ha : d199753 p = 1) (hb : d267709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199725 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199627 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199627, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73356 q ha hb
    | true =>
      simp only [d199627, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73357 q ha hb
  have h3 (q : Pattern) (ha : d199726 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199726, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199726, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199730 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199730, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199730, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199751 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199751, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199751, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199752 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199752, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199752, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199753 q = 1) (hb : d267709 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199753, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199753, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73531 (p : Pattern) (ha : d199866 p = 1) (hb : d267720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199835 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199840 q = 1) (hb : d267715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199840, d267715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73394 q ha hb
    | true =>
      simp only [d199840, d267715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73400 q ha hb
  have h3 (q : Pattern) (ha : d199841 q = 1) (hb : d267716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d199841, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199841, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d199862 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199863 q = 1) (hb : d267717 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d199863, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199863, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199864 q = 1) (hb : d267718 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d199864, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199864, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199865 q = 1) (hb : d267719 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d199865, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199865, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d199866 q = 1) (hb : d267720 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d199866, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199866, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73532 (p : Pattern) (ha : d199879 p = 1) (hb : d267726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199635 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199734 q = 1) (hb : d267078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199734, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73528 q ha hb
    | true =>
      simp only [d199734, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73529 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199748 q = 1) (hb : d267079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199748, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d199748, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d199749 q = 1) (hb : d267707 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199749, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199749, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d199750 q = 1) (hb : d267708 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199750, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199750, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199754 q = 1) (hb : d267710 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199754, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199754, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73530 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d199756 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d199757 q = 1) (hb : d267711 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199757, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d199757, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d199758 q = 1) (hb : d267712 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199758, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d199758, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d199759 q = 1) (hb : d267713 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199759, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d199759, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d199760 q = 1) (hb : d267714 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199760, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199760, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d199867 q = 1) (hb : d267721 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d199867, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d199867, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73531 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d199874 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d199875 q = 1) (hb : d267722 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d199875, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d199875, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d199876 q = 1) (hb : d267723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d199876, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d199876, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d199877 q = 1) (hb : d267724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d199877, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d199877, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d199878 q = 1) (hb : d267725 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d199878, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d199878, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d199879 q = 1) (hb : d267726 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d199879, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d199879, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73533 (p : Pattern) (ha : d199885 p = 1) (hb : d267732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d199880 q = 1) (hb : d267727 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d199880, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199880, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73532 q ha hb
  have h2 (q : Pattern) (ha : d199881 q = 1) (hb : d267728 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d199881, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199881, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d199882 q = 1) (hb : d267729 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d199882, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199882, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199883 q = 1) (hb : d267730 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d199883, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199883, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199884 q = 1) (hb : d267731 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d199884, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199884, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199885 q = 1) (hb : d267732 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d199885, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d199885, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73534 (p : Pattern) (ha : d200035 p = 1) (hb : d267358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199971 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d199999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d199945 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73413 q ha hb
    | true =>
      simp only [d199945, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73414 q ha hb
  have h5 (q : Pattern) (ha : d200000 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d200000, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d200031 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d200032 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200032, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d200033 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d200033, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d200034 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200034, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d200035 q = 1) (hb : d267358 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200035, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200035, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73535 (p : Pattern) (ha : d200056 p = 1) (hb : d267368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199971 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d199980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d199999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d199945 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199945, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73413 q ha hb
    | true =>
      simp only [d199945, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73414 q ha hb
  have h4 (q : Pattern) (ha : d200000 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200000, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d200000, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d200031 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d200032 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200032, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200032, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d200033 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200033, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200033, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200034 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200034, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200034, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d200041 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d200046 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d200048 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d199955 q = 1) (hb : d267363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73416 q ha hb
    | true =>
      simp only [d199955, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73417 q ha hb
  have h13 (q : Pattern) (ha : d200049 q = 1) (hb : d267364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d200049, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d200052 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200053 q = 1) (hb : d267365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200053, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d200054 q = 1) (hb : d267366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200054, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d200054, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d200055 q = 1) (hb : d267367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200055, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d200055, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d200056 q = 1) (hb : d267368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200056, d267368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d200056, d267368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73536 (p : Pattern) (ha : d200076 p = 1) (hb : d267739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d200048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199955 q = 1) (hb : d267363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d199955, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73416 q ha hb
    | true =>
      simp only [d199955, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73417 q ha hb
  have h3 (q : Pattern) (ha : d200049 q = 1) (hb : d267364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200049, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200049, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200053 q = 1) (hb : d267365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200053, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200053, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200074 q = 1) (hb : d267366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200074, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200074, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200075 q = 1) (hb : d267367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200075, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200075, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200076 q = 1) (hb : d267739 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200076, d267739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200076, d267739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73537 (p : Pattern) (ha : d200182 p = 1) (hb : d267750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d200146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d200151 q = 1) (hb : d267745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200151, d267745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73454 q ha hb
    | true =>
      simp only [d200151, d267745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73460 q ha hb
  have h3 (q : Pattern) (ha : d200152 q = 1) (hb : d267746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d200152, d267746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200152, d267746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200179 q = 1) (hb : d267747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d200179, d267747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200179, d267747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200180 q = 1) (hb : d267748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d200180, d267748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200180, d267748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200181 q = 1) (hb : d267749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d200181, d267749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200181, d267749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200182 q = 1) (hb : d267750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d200182, d267750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200182, d267750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73538 (p : Pattern) (ha : d200195 p = 1) (hb : d267756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d199963 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200057 q = 1) (hb : d267369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200057, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73534 q ha hb
    | true =>
      simp only [d200057, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73535 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d200071 q = 1) (hb : d267370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200071, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200071, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d200072 q = 1) (hb : d267737 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200072, d267737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200072, d267737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d200073 q = 1) (hb : d267738 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200073, d267738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200073, d267738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d200077 q = 1) (hb : d267740 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200077, d267740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d200077, d267740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73536 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d200079 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d200080 q = 1) (hb : d267741 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200080, d267741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d200080, d267741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d200081 q = 1) (hb : d267742 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200081, d267742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d200081, d267742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d200082 q = 1) (hb : d267743 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200082, d267743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200082, d267743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d200083 q = 1) (hb : d267744 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200083, d267744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d200083, d267744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200183 q = 1) (hb : d267751 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d200183, d267751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d200183, d267751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73537 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d200190 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d200191 q = 1) (hb : d267752 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d200191, d267752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d200191, d267752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d200192 q = 1) (hb : d267753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d200192, d267753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200192, d267753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d200193 q = 1) (hb : d267754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d200193, d267754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d200193, d267754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d200194 q = 1) (hb : d267755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d200194, d267755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d200194, d267755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d200195 q = 1) (hb : d267756 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d200195, d267756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d200195, d267756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73539 (p : Pattern) (ha : d200201 p = 1) (hb : d267762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200196 q = 1) (hb : d267757 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d200196, d267757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200196, d267757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73538 q ha hb
  have h2 (q : Pattern) (ha : d200197 q = 1) (hb : d267758 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d200197, d267758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200197, d267758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d200198 q = 1) (hb : d267759 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d200198, d267759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200198, d267759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d200199 q = 1) (hb : d267760 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d200199, d267760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200199, d267760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d200200 q = 1) (hb : d267761 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d200200, d267761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200200, d267761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d200201 q = 1) (hb : d267762 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d200201, d267762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d200201, d267762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73540 (p : Pattern) (ha : d200207 p = 1) (hb : d267768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d198937 q = 1) (hb : d267649 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d198937, d267649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73509 q ha hb
    | true =>
      simp only [d198937, d267649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73515 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d199211 q = 1) (hb : d267676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199211, d267676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199211, d267676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73521 q ha hb
  have h3 (q : Pattern) (ha : d199212 q = 1) (hb : d267677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199212, d267677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d199212, d267677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d199548 q = 1) (hb : d267704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199548, d267704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199548, d267704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73527 q ha hb
  have h5 (q : Pattern) (ha : d199549 q = 1) (hb : d267705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199549, d267705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199549, d267705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d199550 q = 1) (hb : d267706 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199550, d267706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d199550, d267706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d199886 q = 1) (hb : d267733 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d199886, d267733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199886, d267733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73533 q ha hb
  have h8 (q : Pattern) (ha : d199887 q = 1) (hb : d267734 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d199887, d267734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199887, d267734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d199888 q = 1) (hb : d267735 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d199888, d267735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d199888, d267735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d199889 q = 1) (hb : d267736 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d199889, d267736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d199889, d267736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d200202 q = 1) (hb : d267763 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d200202, d267763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200202, d267763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73539 q ha hb
  have h12 (q : Pattern) (ha : d200203 q = 1) (hb : d267764 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d200203, d267764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200203, d267764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d200204 q = 1) (hb : d267765 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d200204, d267765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200204, d267765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d200205 q = 1) (hb : d267766 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d200205, d267766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d200205, d267766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d200206 q = 1) (hb : d267767 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d200206, d267767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d200206, d267767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d200207 q = 1) (hb : d267768 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d200207, d267768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d200207, d267768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro73541 (p : Pattern) (ha : d200213 p = 1) (hb : d267774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200208 q = 1) (hb : d267769 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d200208, d267769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73540 q ha hb
    | true =>
      simp only [d200208, d267769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200209 q = 1) (hb : d267770 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d200209, d267770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200209, d267770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200210 q = 1) (hb : d267771 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d200210, d267771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200210, d267771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200211 q = 1) (hb : d267772 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d200211, d267772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200211, d267772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200212 q = 1) (hb : d267773 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d200212, d267773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200212, d267773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200213 q = 1) (hb : d267774 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d200213, d267774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200213, d267774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73542 (p : Pattern) (ha : d200219 p = 1) (hb : d267780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200214 q = 1) (hb : d267775 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d200214, d267775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73541 q ha hb
    | true =>
      simp only [d200214, d267775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200215 q = 1) (hb : d267776 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d200215, d267776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200215, d267776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200216 q = 1) (hb : d267777 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d200216, d267777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200216, d267777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200217 q = 1) (hb : d267778 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d200217, d267778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200217, d267778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200218 q = 1) (hb : d267779 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d200218, d267779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200218, d267779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200219 q = 1) (hb : d267780 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d200219, d267780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200219, d267780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73543 (p : Pattern) (ha : d200225 p = 1) (hb : d267786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200220 q = 1) (hb : d267781 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d200220, d267781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73542 q ha hb
    | true =>
      simp only [d200220, d267781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200221 q = 1) (hb : d267782 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d200221, d267782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200221, d267782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200222 q = 1) (hb : d267783 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d200222, d267783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200222, d267783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200223 q = 1) (hb : d267784 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d200223, d267784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200223, d267784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200224 q = 1) (hb : d267785 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d200224, d267785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200224, d267785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200225 q = 1) (hb : d267786 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d200225, d267786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200225, d267786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73544 (p : Pattern) (ha : d200231 p = 1) (hb : d267792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200226 q = 1) (hb : d267787 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d200226, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73543 q ha hb
    | true =>
      simp only [d200226, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200227 q = 1) (hb : d267788 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d200227, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200227, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200228 q = 1) (hb : d267789 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d200228, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200228, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200229 q = 1) (hb : d267790 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d200229, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200229, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200230 q = 1) (hb : d267791 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d200230, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200230, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200231 q = 1) (hb : d267792 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d200231, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200231, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73545 (p : Pattern) (ha : d200237 p = 1) (hb : d267798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200232 q = 1) (hb : d267793 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d200232, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73544 q ha hb
    | true =>
      simp only [d200232, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200233 q = 1) (hb : d267794 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d200233, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200233, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200234 q = 1) (hb : d267795 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d200234, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200234, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200235 q = 1) (hb : d267796 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d200235, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200235, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200236 q = 1) (hb : d267797 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d200236, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200236, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200237 q = 1) (hb : d267798 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d200237, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200237, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73546 (p : Pattern) (ha : d200243 p = 1) (hb : d267804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200238 q = 1) (hb : d267799 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d200238, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73545 q ha hb
    | true =>
      simp only [d200238, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200239 q = 1) (hb : d267800 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d200239, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200239, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200240 q = 1) (hb : d267801 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d200240, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200240, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200241 q = 1) (hb : d267802 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d200241, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200241, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200242 q = 1) (hb : d267803 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d200242, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200242, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200243 q = 1) (hb : d267804 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d200243, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200243, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73547 (p : Pattern) (ha : d200249 p = 1) (hb : d267810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d200244 q = 1) (hb : d267805 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d200244, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73546 q ha hb
    | true =>
      simp only [d200244, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d200245 q = 1) (hb : d267806 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d200245, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d200245, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d200246 q = 1) (hb : d267807 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d200246, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d200246, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d200247 q = 1) (hb : d267808 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d200247, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d200247, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d200248 q = 1) (hb : d267809 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d200248, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d200248, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d200249 q = 1) (hb : d267810 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d200249, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d200249, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73548 (p : Pattern) (ha : d25187 p = 1) (hb : d202015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25209 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25240 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25183 q = 1) (hb : d202011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d202011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25183, d202011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25269 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25184 q = 1) (hb : d202012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d202012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25184, d202012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25185 q = 1) (hb : d202013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d202013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25185, d202013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25186 q = 1) (hb : d202014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d202014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25186, d202014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25187 q = 1) (hb : d202015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d202015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d202015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73549 (p : Pattern) (ha : d25194 p = 1) (hb : d202020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25203 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25240 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25123 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25183 q = 1) (hb : d202011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d202011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25183, d202011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25269 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25184 q = 1) (hb : d202012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d202012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25184, d202012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25185 q = 1) (hb : d202013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d202013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25185, d202013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25186 q = 1) (hb : d202014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d202014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d202014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25278 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25282 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25284 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d25130 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d25190 q = 1) (hb : d202016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d202016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25190, d202016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25290 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25191 q = 1) (hb : d202017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d202017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25191, d202017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25192 q = 1) (hb : d202018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d202018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25192, d202018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25193 q = 1) (hb : d202019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d202019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25193, d202019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d25194 q = 1) (hb : d202020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d202020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25194, d202020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73550 (p : Pattern) (ha : d202027 p = 1) (hb : d245682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25190 q = 1) (hb : d202016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d202016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25190, d202016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25290 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25191 q = 1) (hb : d202017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d202017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25191, d202017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25192 q = 1) (hb : d202025 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d202025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d202025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25193 q = 1) (hb : d202026 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d202026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d202026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202027 q = 1) (hb : d245682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d245682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202027, d245682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro73551 (p : Pattern) (ha : d202037 p = 1) (hb : d245692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25332 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25166 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202033 q = 1) (hb : d245688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d245688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202033, d245688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202034 q = 1) (hb : d245689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d245689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202034, d245689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202035 q = 1) (hb : d245690 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d245690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202035, d245690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202036 q = 1) (hb : d245691 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d245691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202036, d245691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202037 q = 1) (hb : d245692 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d245692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202037, d245692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73552 (p : Pattern) (ha : d202043 p = 1) (hb : d245698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25197 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d202021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d202021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73548 q ha hb
    | true =>
      simp only [d25195, d202021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73549 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25196 q = 1) (hb : d202022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d202022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d202022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202023 q = 1) (hb : d245680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d245680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202023, d245680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202024 q = 1) (hb : d245681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d245681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202024, d245681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202028 q = 1) (hb : d245683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d245683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202028, d245683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73550 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202029 q = 1) (hb : d245684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d245684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202029, d245684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202030 q = 1) (hb : d245685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d245685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202030, d245685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202031 q = 1) (hb : d245686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d245686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202031, d245686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202032 q = 1) (hb : d245687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d245687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202032, d245687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202038 q = 1) (hb : d245693 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d245693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202038, d245693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73551 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202039 q = 1) (hb : d245694 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d245694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202039, d245694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202040 q = 1) (hb : d245695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d245695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202040, d245695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202041 q = 1) (hb : d245696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d245696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202041, d245696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202042 q = 1) (hb : d245697 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d245697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202042, d245697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202043 q = 1) (hb : d245698 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d245698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202043, d245698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73553 (p : Pattern) (ha : d202049 p = 1) (hb : d245704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d202006 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d202006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47842 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d202007 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d202007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d202008 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d202008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d202009 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d202009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d202010 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d202010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202044 q = 1) (hb : d245699 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d245699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202044, d245699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73552 q ha hb
  have h8 (q : Pattern) (ha : d202045 q = 1) (hb : d245700 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d245700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202045, d245700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202046 q = 1) (hb : d245701 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d245701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202046, d245701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202047 q = 1) (hb : d245702 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d245702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202047, d245702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202048 q = 1) (hb : d245703 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d245703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202048, d245703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d202049 q = 1) (hb : d245704 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d245704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d202049, d245704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro73554 (p : Pattern) (ha : d202054 p = 1) (hb : d266340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25418 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25474 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d266335 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202050 q = 1) (hb : d266336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202050, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25521 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202051 q = 1) (hb : d266337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202051, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202052 q = 1) (hb : d266338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202052, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202053 q = 1) (hb : d266339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202053, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202054 q = 1) (hb : d266340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202054, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73555 (p : Pattern) (ha : d202059 p = 1) (hb : d266349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25418 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25427 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25474 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266335 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202050 q = 1) (hb : d266336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202050, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25521 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202051 q = 1) (hb : d266337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202051, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202052 q = 1) (hb : d266338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202052, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202053 q = 1) (hb : d266339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202053, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25531 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25536 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25538 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d266344 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202055 q = 1) (hb : d266345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202055, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202056 q = 1) (hb : d266346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202056, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202057 q = 1) (hb : d266347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202057, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202058 q = 1) (hb : d266348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202058, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202059 q = 1) (hb : d266349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202059, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73556 (p : Pattern) (ha : d202066 p = 1) (hb : d267625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25538 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d266344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202055 q = 1) (hb : d266345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202055, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25545 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202056 q = 1) (hb : d266346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202056, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202064 q = 1) (hb : d266347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202064, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202065 q = 1) (hb : d266348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202065, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202066 q = 1) (hb : d267625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202066, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73557 (p : Pattern) (ha : d202076 p = 1) (hb : d267636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267631 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202072 q = 1) (hb : d267632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202072, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202072, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25661 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202073 q = 1) (hb : d267633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202073, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202073, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202074 q = 1) (hb : d267634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202074, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202074, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202075 q = 1) (hb : d267635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202075, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202075, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202076 q = 1) (hb : d267636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202076, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202076, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73558 (p : Pattern) (ha : d202082 p = 1) (hb : d267642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25410 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202060 q = 1) (hb : d266350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202060, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73554 q ha hb
    | true =>
      simp only [d202060, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73555 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202061 q = 1) (hb : d266351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202061, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202061, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202062 q = 1) (hb : d267623 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202062, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202062, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202063 q = 1) (hb : d267624 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202063, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202063, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202067 q = 1) (hb : d267626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202067, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202067, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73556 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25572 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202068 q = 1) (hb : d267627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202068, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202068, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202069 q = 1) (hb : d267628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202069, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202069, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202070 q = 1) (hb : d267629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202070, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202070, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202071 q = 1) (hb : d267630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202071, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202071, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202077 q = 1) (hb : d267637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202077, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202077, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73557 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202078 q = 1) (hb : d267638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202078, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202078, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202079 q = 1) (hb : d267639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202079, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202079, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202080 q = 1) (hb : d267640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202080, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202080, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202081 q = 1) (hb : d267641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202081, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202081, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202082 q = 1) (hb : d267642 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202082, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202082, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73559 (p : Pattern) (ha : d202088 p = 1) (hb : d267648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202083 q = 1) (hb : d267643 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202083, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202083, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73558 q ha hb
  have h2 (q : Pattern) (ha : d202084 q = 1) (hb : d267644 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202084, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202084, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202085 q = 1) (hb : d267645 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202085, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202085, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202086 q = 1) (hb : d267646 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202086, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202086, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202087 q = 1) (hb : d267647 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202087, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202087, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202088 q = 1) (hb : d267648 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202088, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202088, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73560 (p : Pattern) (ha : d202094 p = 1) (hb : d266529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25760 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25806 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d266524 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202090 q = 1) (hb : d266525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202090, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25877 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202091 q = 1) (hb : d266526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202091, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202092 q = 1) (hb : d266527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202092, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202093 q = 1) (hb : d266528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202093, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202094 q = 1) (hb : d266529 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202094, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202094, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73561 (p : Pattern) (ha : d202099 p = 1) (hb : d266539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25806 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266524 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202090 q = 1) (hb : d266525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202090, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d25877 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202091 q = 1) (hb : d266526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202091, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202092 q = 1) (hb : d266527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202092, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202093 q = 1) (hb : d266528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202093, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d25887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25892 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d25894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d266534 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202095 q = 1) (hb : d266535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202095, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202096 q = 1) (hb : d266536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202096, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202097 q = 1) (hb : d266537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202097, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202097, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202098 q = 1) (hb : d266538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202098, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202098, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202099 q = 1) (hb : d266539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202099, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202099, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73562 (p : Pattern) (ha : d202106 p = 1) (hb : d267652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d266534 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202095 q = 1) (hb : d266535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202095, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202096 q = 1) (hb : d266536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202096, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202104 q = 1) (hb : d266537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202104, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202104, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202105 q = 1) (hb : d266538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202105, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202105, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202106 q = 1) (hb : d267652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202106, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202106, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73563 (p : Pattern) (ha : d202116 p = 1) (hb : d267663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202112 q = 1) (hb : d267659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202112, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202112, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26049 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202113 q = 1) (hb : d267660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202113, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202113, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202114 q = 1) (hb : d267661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202114, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202114, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202115 q = 1) (hb : d267662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202115, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202115, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202116 q = 1) (hb : d267663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202116, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202116, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73564 (p : Pattern) (ha : d202122 p = 1) (hb : d267669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25743 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202100 q = 1) (hb : d266540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202100, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73560 q ha hb
    | true =>
      simp only [d202100, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73561 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202101 q = 1) (hb : d266541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202101, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202101, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202102 q = 1) (hb : d267650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202102, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202102, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202103 q = 1) (hb : d267651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202103, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202103, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202107 q = 1) (hb : d267653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202107, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202107, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73562 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d25928 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202108 q = 1) (hb : d267654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202108, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202108, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202109 q = 1) (hb : d267655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202109, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202109, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202110 q = 1) (hb : d267656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202110, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202110, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202111 q = 1) (hb : d267657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202111, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202111, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202117 q = 1) (hb : d267664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202117, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202117, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73563 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26065 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202118 q = 1) (hb : d267665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202118, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202118, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202119 q = 1) (hb : d267666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202119, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202119, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202120 q = 1) (hb : d267667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202120, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202120, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202121 q = 1) (hb : d267668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202121, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202121, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202122 q = 1) (hb : d267669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202122, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202122, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73565 (p : Pattern) (ha : d202128 p = 1) (hb : d267675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202123 q = 1) (hb : d267670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202123, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202123, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73564 q ha hb
  have h2 (q : Pattern) (ha : d202124 q = 1) (hb : d267671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202124, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202124, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202125 q = 1) (hb : d267672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202125, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202125, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202126 q = 1) (hb : d267673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202126, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202126, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202127 q = 1) (hb : d267674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202127, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202127, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202128 q = 1) (hb : d267675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202128, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202128, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73566 (p : Pattern) (ha : d202135 p = 1) (hb : d266774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d26222 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d266769 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202131 q = 1) (hb : d266770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202131, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26317 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202132 q = 1) (hb : d266771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202132, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202133 q = 1) (hb : d266772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202133, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202134 q = 1) (hb : d266773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202134, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202135 q = 1) (hb : d266774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202135, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202135, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73567 (p : Pattern) (ha : d202140 p = 1) (hb : d266784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266769 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202131 q = 1) (hb : d266770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202131, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202132 q = 1) (hb : d266771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202132, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202133 q = 1) (hb : d266772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202133, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202134 q = 1) (hb : d266773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202134, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26327 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26332 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d26334 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d266779 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202136 q = 1) (hb : d266780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202136, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26341 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202137 q = 1) (hb : d266781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202137, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202138 q = 1) (hb : d266782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202138, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202138, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202139 q = 1) (hb : d266783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202139, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202139, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202140 q = 1) (hb : d266784 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202140, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202140, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73568 (p : Pattern) (ha : d202147 p = 1) (hb : d267680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d266779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202136 q = 1) (hb : d266780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202136, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26341 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202137 q = 1) (hb : d266781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202137, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202145 q = 1) (hb : d266782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202145, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202145, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202146 q = 1) (hb : d266783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202146, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202146, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202147 q = 1) (hb : d267680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202147, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202147, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73569 (p : Pattern) (ha : d202157 p = 1) (hb : d267691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26451 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202153 q = 1) (hb : d267687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202153, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202153, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26519 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202154 q = 1) (hb : d267688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202154, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202154, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202155 q = 1) (hb : d267689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202155, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202155, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202156 q = 1) (hb : d267690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202156, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202156, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202157 q = 1) (hb : d267691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202157, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202157, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73570 (p : Pattern) (ha : d202163 p = 1) (hb : d267697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202141 q = 1) (hb : d266785 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202141, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73566 q ha hb
    | true =>
      simp only [d202141, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73567 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202142 q = 1) (hb : d266786 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202142, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202142, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202143 q = 1) (hb : d267678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202143, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202143, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202144 q = 1) (hb : d267679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202144, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202144, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202148 q = 1) (hb : d267681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202148, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202148, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73568 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d26368 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202149 q = 1) (hb : d267682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202149, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202149, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202150 q = 1) (hb : d267683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202150, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202150, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202151 q = 1) (hb : d267684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202151, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202151, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202152 q = 1) (hb : d267685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202152, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202152, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202158 q = 1) (hb : d267692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202158, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202158, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73569 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26535 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202159 q = 1) (hb : d267693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202159, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202159, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202160 q = 1) (hb : d267694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202160, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202160, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202161 q = 1) (hb : d267695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202161, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202161, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202162 q = 1) (hb : d267696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202162, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202162, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202163 q = 1) (hb : d267697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202163, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202163, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73571 (p : Pattern) (ha : d202169 p = 1) (hb : d267703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202164 q = 1) (hb : d267698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202164, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202164, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73570 q ha hb
  have h2 (q : Pattern) (ha : d202165 q = 1) (hb : d267699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202165, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202165, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202166 q = 1) (hb : d267700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202166, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202166, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202167 q = 1) (hb : d267701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202167, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202167, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202168 q = 1) (hb : d267702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202168, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202168, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202169 q = 1) (hb : d267703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202169, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202169, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73572 (p : Pattern) (ha : d202177 p = 1) (hb : d267067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26651 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d26681 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202173 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202173, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d26778 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202174 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202174, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202175 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202175, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202176 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202176, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202177 q = 1) (hb : d267067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202177, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202177, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73573 (p : Pattern) (ha : d202182 p = 1) (hb : d267077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202173 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202173, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d26778 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202174 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202174, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202175 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202175, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202176 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202176, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d26788 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d26793 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d26795 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202178 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202178, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26802 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202179 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202179, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202180 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202180, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202180, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202181 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202181, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202181, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202182 q = 1) (hb : d267077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202182, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202182, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73574 (p : Pattern) (ha : d202189 p = 1) (hb : d267709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202178 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202178, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26802 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202179 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202179, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202187 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202187, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202187, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202188 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202188, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202188, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202189 q = 1) (hb : d267709 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202189, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202189, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73575 (p : Pattern) (ha : d202199 p = 1) (hb : d267720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267715 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202195 q = 1) (hb : d267716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202195, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202195, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d26982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202196 q = 1) (hb : d267717 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202196, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202196, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202197 q = 1) (hb : d267718 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202197, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202197, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202198 q = 1) (hb : d267719 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202198, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202198, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202199 q = 1) (hb : d267720 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202199, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202199, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73576 (p : Pattern) (ha : d202205 p = 1) (hb : d267726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d26634 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202183 q = 1) (hb : d267078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202183, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73572 q ha hb
    | true =>
      simp only [d202183, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73573 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d26820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202184 q = 1) (hb : d267079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202184, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202184, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202185 q = 1) (hb : d267707 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202185, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202185, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202186 q = 1) (hb : d267708 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202186, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202186, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202190 q = 1) (hb : d267710 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202190, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202190, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73574 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d26829 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202191 q = 1) (hb : d267711 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202191, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202191, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202192 q = 1) (hb : d267712 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202192, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202192, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202193 q = 1) (hb : d267713 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202193, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202193, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202194 q = 1) (hb : d267714 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202194, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202194, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202200 q = 1) (hb : d267721 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202200, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202200, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73575 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d26998 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202201 q = 1) (hb : d267722 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202201, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202201, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202202 q = 1) (hb : d267723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202202, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202202, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202203 q = 1) (hb : d267724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202203, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202203, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202204 q = 1) (hb : d267725 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202204, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202204, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202205 q = 1) (hb : d267726 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202205, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202205, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73577 (p : Pattern) (ha : d202211 p = 1) (hb : d267732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202206 q = 1) (hb : d267727 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202206, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202206, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73576 q ha hb
  have h2 (q : Pattern) (ha : d202207 q = 1) (hb : d267728 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202207, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202207, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202208 q = 1) (hb : d267729 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202208, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202208, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202209 q = 1) (hb : d267730 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202209, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202209, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202210 q = 1) (hb : d267731 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202210, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202210, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202211 q = 1) (hb : d267732 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202211, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202211, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73578 (p : Pattern) (ha : d202220 p = 1) (hb : d267358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d27123 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202216 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d202216, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d27211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d202217 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202217, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d202218 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202218, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202219 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202219, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202220 q = 1) (hb : d267358 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202220, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202220, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73579 (p : Pattern) (ha : d202225 p = 1) (hb : d267368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27095 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27104 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27123 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d202216 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d202216, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d27211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d202217 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202217, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d202218 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202218, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202219 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202219, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d27221 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d27226 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d27228 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d267363 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d202221 q = 1) (hb : d267364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d202221, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27235 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202222 q = 1) (hb : d267365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202222, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202223 q = 1) (hb : d267366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202223, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d202223, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202224 q = 1) (hb : d267367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202224, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d202224, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d202225 q = 1) (hb : d267368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202225, d267368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202225, d267368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73580 (p : Pattern) (ha : d202232 p = 1) (hb : d267739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27228 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267363 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202221 q = 1) (hb : d267364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202221, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202222 q = 1) (hb : d267365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202222, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202230 q = 1) (hb : d267366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202230, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202230, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202231 q = 1) (hb : d267367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202231, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202231, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202232 q = 1) (hb : d267739 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202232, d267739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202232, d267739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73581 (p : Pattern) (ha : d202242 p = 1) (hb : d267750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27329 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202238 q = 1) (hb : d267746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202238, d267746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202238, d267746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d27405 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202239 q = 1) (hb : d267747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202239, d267747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202239, d267747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d202240 q = 1) (hb : d267748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202240, d267748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202240, d267748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202241 q = 1) (hb : d267749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202241, d267749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202241, d267749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202242 q = 1) (hb : d267750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202242, d267750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202242, d267750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73582 (p : Pattern) (ha : d202248 p = 1) (hb : d267756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d27087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202226 q = 1) (hb : d267369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202226, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73578 q ha hb
    | true =>
      simp only [d202226, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73579 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d27253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d202227 q = 1) (hb : d267370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202227, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202227, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d202228 q = 1) (hb : d267737 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202228, d267737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202228, d267737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202229 q = 1) (hb : d267738 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202229, d267738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202229, d267738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202233 q = 1) (hb : d267740 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202233, d267740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202233, d267740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73580 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d27262 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d202234 q = 1) (hb : d267741 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202234, d267741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202234, d267741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d202235 q = 1) (hb : d267742 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202235, d267742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202235, d267742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d202236 q = 1) (hb : d267743 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202236, d267743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202236, d267743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d202237 q = 1) (hb : d267744 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202237, d267744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202237, d267744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202243 q = 1) (hb : d267751 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202243, d267751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202243, d267751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73581 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d27421 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d202244 q = 1) (hb : d267752 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202244, d267752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202244, d267752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d202245 q = 1) (hb : d267753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202245, d267753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202245, d267753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d202246 q = 1) (hb : d267754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202246, d267754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202246, d267754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d202247 q = 1) (hb : d267755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202247, d267755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202247, d267755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d202248 q = 1) (hb : d267756 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202248, d267756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d202248, d267756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73583 (p : Pattern) (ha : d202254 p = 1) (hb : d267762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202249 q = 1) (hb : d267757 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202249, d267757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202249, d267757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73582 q ha hb
  have h2 (q : Pattern) (ha : d202250 q = 1) (hb : d267758 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202250, d267758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202250, d267758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202251 q = 1) (hb : d267759 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202251, d267759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202251, d267759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202252 q = 1) (hb : d267760 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202252, d267760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202252, d267760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202253 q = 1) (hb : d267761 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202253, d267761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202253, d267761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202254 q = 1) (hb : d267762 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202254, d267762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202254, d267762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73584 (p : Pattern) (ha : d202260 p = 1) (hb : d267768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d202089 q = 1) (hb : d267649 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202089, d267649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73553 q ha hb
    | true =>
      simp only [d202089, d267649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73559 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d202129 q = 1) (hb : d267676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202129, d267676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202129, d267676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73565 q ha hb
  have h3 (q : Pattern) (ha : d202130 q = 1) (hb : d267677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202130, d267677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202130, d267677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202170 q = 1) (hb : d267704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202170, d267704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202170, d267704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73571 q ha hb
  have h5 (q : Pattern) (ha : d202171 q = 1) (hb : d267705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202171, d267705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202171, d267705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202172 q = 1) (hb : d267706 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202172, d267706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202172, d267706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202212 q = 1) (hb : d267733 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202212, d267733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202212, d267733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73577 q ha hb
  have h8 (q : Pattern) (ha : d202213 q = 1) (hb : d267734 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202213, d267734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202213, d267734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202214 q = 1) (hb : d267735 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202214, d267735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202214, d267735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202215 q = 1) (hb : d267736 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d202215, d267736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202215, d267736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202255 q = 1) (hb : d267763 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202255, d267763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202255, d267763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73583 q ha hb
  have h12 (q : Pattern) (ha : d202256 q = 1) (hb : d267764 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202256, d267764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202256, d267764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202257 q = 1) (hb : d267765 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202257, d267765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202257, d267765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202258 q = 1) (hb : d267766 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d202258, d267766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202258, d267766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202259 q = 1) (hb : d267767 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d202259, d267767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202259, d267767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202260 q = 1) (hb : d267768 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d202260, d267768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202260, d267768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro73585 (p : Pattern) (ha : d202266 p = 1) (hb : d267774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202261 q = 1) (hb : d267769 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d202261, d267769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73584 q ha hb
    | true =>
      simp only [d202261, d267769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202262 q = 1) (hb : d267770 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d202262, d267770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202262, d267770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202263 q = 1) (hb : d267771 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d202263, d267771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202263, d267771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202264 q = 1) (hb : d267772 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d202264, d267772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202264, d267772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202265 q = 1) (hb : d267773 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d202265, d267773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202265, d267773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202266 q = 1) (hb : d267774 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d202266, d267774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202266, d267774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73586 (p : Pattern) (ha : d202272 p = 1) (hb : d267780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202267 q = 1) (hb : d267775 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d202267, d267775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73585 q ha hb
    | true =>
      simp only [d202267, d267775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202268 q = 1) (hb : d267776 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d202268, d267776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202268, d267776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202269 q = 1) (hb : d267777 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d202269, d267777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202269, d267777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202270 q = 1) (hb : d267778 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d202270, d267778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202270, d267778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202271 q = 1) (hb : d267779 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d202271, d267779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202271, d267779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202272 q = 1) (hb : d267780 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d202272, d267780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202272, d267780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73587 (p : Pattern) (ha : d202278 p = 1) (hb : d267786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202273 q = 1) (hb : d267781 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d202273, d267781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73586 q ha hb
    | true =>
      simp only [d202273, d267781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202274 q = 1) (hb : d267782 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d202274, d267782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202274, d267782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202275 q = 1) (hb : d267783 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d202275, d267783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202275, d267783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202276 q = 1) (hb : d267784 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d202276, d267784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202276, d267784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202277 q = 1) (hb : d267785 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d202277, d267785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202277, d267785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202278 q = 1) (hb : d267786 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d202278, d267786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202278, d267786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73588 (p : Pattern) (ha : d202284 p = 1) (hb : d267792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202279 q = 1) (hb : d267787 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d202279, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73587 q ha hb
    | true =>
      simp only [d202279, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202280 q = 1) (hb : d267788 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d202280, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202280, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202281 q = 1) (hb : d267789 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d202281, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202281, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202282 q = 1) (hb : d267790 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d202282, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202282, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202283 q = 1) (hb : d267791 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d202283, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202283, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202284 q = 1) (hb : d267792 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d202284, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202284, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73589 (p : Pattern) (ha : d202290 p = 1) (hb : d267798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202285 q = 1) (hb : d267793 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d202285, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73588 q ha hb
    | true =>
      simp only [d202285, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202286 q = 1) (hb : d267794 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d202286, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202286, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202287 q = 1) (hb : d267795 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d202287, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202287, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202288 q = 1) (hb : d267796 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d202288, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202288, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202289 q = 1) (hb : d267797 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d202289, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202289, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202290 q = 1) (hb : d267798 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d202290, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202290, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73590 (p : Pattern) (ha : d202296 p = 1) (hb : d267804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202291 q = 1) (hb : d267799 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d202291, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73589 q ha hb
    | true =>
      simp only [d202291, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202292 q = 1) (hb : d267800 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d202292, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202292, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202293 q = 1) (hb : d267801 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d202293, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202293, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202294 q = 1) (hb : d267802 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d202294, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202294, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202295 q = 1) (hb : d267803 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d202295, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202295, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202296 q = 1) (hb : d267804 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d202296, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202296, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73591 (p : Pattern) (ha : d202302 p = 1) (hb : d267810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202297 q = 1) (hb : d267805 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d202297, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73590 q ha hb
    | true =>
      simp only [d202297, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202298 q = 1) (hb : d267806 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d202298, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202298, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202299 q = 1) (hb : d267807 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d202299, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202299, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202300 q = 1) (hb : d267808 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d202300, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202300, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202301 q = 1) (hb : d267809 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d202301, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202301, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202302 q = 1) (hb : d267810 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d202302, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202302, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73592 (p : Pattern) (ha : d236583 p = 1) (hb : d239099 p = 1) : d238713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d239094 q = 1) : d238708 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d236583, d239094, d238708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70700 q ha hb
    | true =>
      simp only [d236583, d239094, d238708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d239095 q = 1) : d238709 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d239095, d238709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239095, d238709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d239096 q = 1) : d238710 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d239096, d238710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239096, d238710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d239097 q = 1) : d238711 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d239097, d238711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239097, d238711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d239098 q = 1) : d238712 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d239098, d238712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239098, d238712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d236583 q = 1) (hb : d239099 q = 1) : d238713 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d239099, d238713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d239099, d238713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro73593 (p : Pattern) (ha : d236583 p = 1) (hb : d239105 p = 1) : d238719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d239100 q = 1) : d238714 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d239100, d238714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73592 q ha hb
    | true =>
      simp only [d239100, d238714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d236583 q = 1) (hb : d239101 q = 1) : d238715 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d239101, d238715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239101, d238715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d239102 q = 1) : d238716 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d239102, d238716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239102, d238716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d239103 q = 1) : d238717 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d239103, d238717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239103, d238717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d239104 q = 1) : d238718 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d239104, d238718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239104, d238718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d239105 q = 1) : d238719 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d239105, d238719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239105, d238719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73594 (p : Pattern) (ha : d236583 p = 1) (hb : d239111 p = 1) : d238725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d239106 q = 1) : d238720 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d239106, d238720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73593 q ha hb
    | true =>
      simp only [d239106, d238720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d236583 q = 1) (hb : d239107 q = 1) : d238721 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d239107, d238721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239107, d238721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d239108 q = 1) : d238722 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d239108, d238722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239108, d238722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d239109 q = 1) : d238723 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d239109, d238723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239109, d238723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d239110 q = 1) : d238724 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d239110, d238724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239110, d238724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d239111 q = 1) : d238725 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d239111, d238725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239111, d238725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73595 (p : Pattern) (ha : d236583 p = 1) (hb : d239117 p = 1) : d238731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d239112 q = 1) : d238726 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d239112, d238726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73594 q ha hb
    | true =>
      simp only [d239112, d238726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d236583 q = 1) (hb : d239113 q = 1) : d238727 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d239113, d238727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239113, d238727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d239114 q = 1) : d238728 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d239114, d238728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239114, d238728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d239115 q = 1) : d238729 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d239115, d238729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239115, d238729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d239116 q = 1) : d238730 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d239116, d238730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239116, d238730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d239117 q = 1) : d238731 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d239117, d238731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239117, d238731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73596 (p : Pattern) (ha : d236583 p = 1) (hb : d239123 p = 1) : d238737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d239118 q = 1) : d238732 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d239118, d238732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73595 q ha hb
    | true =>
      simp only [d239118, d238732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d236583 q = 1) (hb : d239119 q = 1) : d238733 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d239119, d238733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239119, d238733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d239120 q = 1) : d238734 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d239120, d238734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239120, d238734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d239121 q = 1) : d238735 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d239121, d238735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239121, d238735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d239122 q = 1) : d238736 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d239122, d238736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239122, d238736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d239123 q = 1) : d238737 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d239123, d238737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239123, d238737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73597 (p : Pattern) (ha : d23421 p = 1) (hb : d52690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52668 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d531, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52674 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d313 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d314 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d314, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d533 q = 1) (hb : d52677 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23419 q = 1) (hb : d52678 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23419, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23420 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23420, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d133 q = 1) (hb : d52685 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d134 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d134, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d315 q = 1) (hb : d52687 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d315, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d23228 q = 1) (hb : d52688 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23228, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23229 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23229, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d23421 q = 1) (hb : d52690 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23421, d52690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23421, d52690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73598 (p : Pattern) (ha : d23694 p = 1) (hb : d52680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d52499 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro120 q ha hb
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d823 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52668 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d531, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d52671 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d824, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52507 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d23692 q = 1) (hb : d52672 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23692, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23692, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d23693 q = 1) (hb : d52673 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23693, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23693, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52674 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d313 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d314 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d314, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d533 q = 1) (hb : d52677 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d52677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52286 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d23419 q = 1) (hb : d52678 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23419, d52678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d23420 q = 1) (hb : d52679 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23420, d52679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d23694 q = 1) (hb : d52680 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23694, d52680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23694, d52680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro73599 (p : Pattern) (ha : d52701 p = 1) (hb : d237981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52674 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d52675 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d52676 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d52676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51870 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d133 q = 1) (hb : d52685 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d134 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d134, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d315 q = 1) (hb : d52687 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d52687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d23228 q = 1) (hb : d52688 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23228, d52688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23229 q = 1) (hb : d52689 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23229, d52689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52697 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d29090 q = 1) (hb : d52698 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29090, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29090, d52698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d52699 q = 1) (hb : d205892 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d52699, d205892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d52699, d205892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d52700 q = 1) (hb : d205893 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d52700, d205893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52700, d205893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h18 (q : Pattern) (ha : d52701 q = 1) (hb : d237981 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d52701, d237981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d52701, d237981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73600 (p : Pattern) (ha : d52707 p = 1) (hb : d237987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23695 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73598 q ha hb
    | true =>
      simp only [d23695, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23696 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23696, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23697 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23697, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23697, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23698 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23698, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23698, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23422 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
    | true =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23423 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23424 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23425 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23425, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23699 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23699, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23699, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52702 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
    | true =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d52703 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d52704 q = 1) (hb : d237984 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52704, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52704, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52705 q = 1) (hb : d237985 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52705, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52705, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d52706 q = 1) (hb : d237986 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52706, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52706, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52707 q = 1) (hb : d237987 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52707, d237987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52707, d237987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73601 (p : Pattern) (ha : d52709 p = 1) (hb : d237989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
    | true =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d52702 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
    | true =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52703 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52704 q = 1) (hb : d237984 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52704, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52704, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52705 q = 1) (hb : d237985 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52705, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52705, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52706 q = 1) (hb : d237986 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52706, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52706, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52708 q = 1) (hb : d237988 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52708, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52708, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d52709 q = 1) (hb : d237989 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52709, d237989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52709, d237989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73602 (p : Pattern) (ha : d52722 p = 1) (hb : d237993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52702 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
    | true =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52703 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d52704 q = 1) (hb : d237984 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52704, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52704, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52705 q = 1) (hb : d237985 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52705, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52705, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52708 q = 1) (hb : d237988 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52708, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52708, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52721 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52722 q = 1) (hb : d237993 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52722, d237993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52722, d237993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro73603 (p : Pattern) (ha : d52729 p = 1) (hb : d238000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52710 q = 1) (hb : d237990 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52710, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73600 q ha hb
    | true =>
      simp only [d52710, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73601 q ha hb
  have h2 (q : Pattern) (ha : d52711 q = 1) (hb : d237991 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52711, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52711, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52712 q = 1) (hb : d237992 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52712, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52712, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52723 q = 1) (hb : d237994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52723, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73601 q ha hb
    | true =>
      simp only [d52723, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73602 q ha hb
  have h5 (q : Pattern) (ha : d52724 q = 1) (hb : d237995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52724, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52724, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52725 q = 1) (hb : d237996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52725, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52725, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52726 q = 1) (hb : d237997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52726, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52726, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52727 q = 1) (hb : d237998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52727, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52727, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52728 q = 1) (hb : d237999 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52728, d237999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52728, d237999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52729 q = 1) (hb : d238000 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52729, d238000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52729, d238000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro73604 (p : Pattern) (ha : d52733 p = 1) (hb : d238004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52723 q = 1) (hb : d237994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52723, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73601 q ha hb
    | true =>
      simp only [d52723, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73602 q ha hb
  have h2 (q : Pattern) (ha : d52724 q = 1) (hb : d237995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52724, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52724, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52725 q = 1) (hb : d237996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52725, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52725, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52727 q = 1) (hb : d237998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52727, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52727, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52732 q = 1) (hb : d238003 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52732, d238003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52732, d238003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52733 q = 1) (hb : d238004 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52733, d238004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52733, d238004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73605 (p : Pattern) (ha : d52739 p = 1) (hb : d238010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52730 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73603 q ha hb
    | true =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52731 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52736 q = 1) (hb : d238007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52737 q = 1) (hb : d238008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52737, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52737, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52738 q = 1) (hb : d238009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52738, d238009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52738, d238009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52739 q = 1) (hb : d238010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52739, d238010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52739, d238010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73606 (p : Pattern) (ha : d52743 p = 1) (hb : d238014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d238011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52741 q = 1) (hb : d238012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52741, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52741, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52742 q = 1) (hb : d238013 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52742, d238013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52742, d238013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52743 q = 1) (hb : d238014 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52743, d238014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52743, d238014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73607 (p : Pattern) (ha : d52749 p = 1) (hb : d238020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52744 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73605 q ha hb
    | true =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73606 q ha hb
  have h2 (q : Pattern) (ha : d52745 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52745, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52745, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52746 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52746, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52746, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52747 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52747, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52747, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52748 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52748, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52748, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52749 q = 1) (hb : d238020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52749, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52749, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73608 (p : Pattern) (ha : d52752 p = 1) (hb : d238023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52730 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73603 q ha hb
    | true =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52731 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52736 q = 1) (hb : d238007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52737 q = 1) (hb : d238008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52737, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52737, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52738 q = 1) (hb : d238009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52738, d238009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52738, d238009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52752 q = 1) (hb : d238023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52752, d238023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52752, d238023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73609 (p : Pattern) (ha : d52753 p = 1) (hb : d238024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d238011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52741 q = 1) (hb : d238012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52741, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52741, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52742 q = 1) (hb : d238013 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52742, d238013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52742, d238013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52753 q = 1) (hb : d238024 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52753, d238024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52753, d238024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73610 (p : Pattern) (ha : d52759 p = 1) (hb : d238030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52744 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73605 q ha hb
    | true =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73606 q ha hb
  have h2 (q : Pattern) (ha : d52745 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52745, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52745, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52746 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52746, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52746, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52747 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52747, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52747, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52748 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52748, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52748, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52754 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52754, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73608 q ha hb
    | true =>
      simp only [d52754, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73609 q ha hb
  have h7 (q : Pattern) (ha : d52755 q = 1) (hb : d238026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52755, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52755, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52756 q = 1) (hb : d238027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52756, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52756, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52757 q = 1) (hb : d238028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52757, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52757, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52758 q = 1) (hb : d238029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52758, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52758, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52759 q = 1) (hb : d238030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52759, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52759, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73611 (p : Pattern) (ha : d52843 p = 1) (hb : d238109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52744 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73605 q ha hb
    | true =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73606 q ha hb
  have h2 (q : Pattern) (ha : d52745 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52745, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52745, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52746 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52746, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52746, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52747 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52747, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52747, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52748 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52748, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52748, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52838 q = 1) (hb : d238104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52838, d238104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73606 q ha hb
    | true =>
      simp only [d52838, d238104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52839 q = 1) (hb : d238105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52839, d238105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52839, d238105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52840 q = 1) (hb : d238106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52840, d238106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52840, d238106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52841 q = 1) (hb : d238107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52841, d238107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52841, d238107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52842 q = 1) (hb : d238108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52842, d238108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52842, d238108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52843 q = 1) (hb : d238109 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52843, d238109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52843, d238109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73612 (p : Pattern) (ha : d52849 p = 1) (hb : d238115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52838 q = 1) (hb : d238104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52838, d238104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73606 q ha hb
    | true =>
      simp only [d52838, d238104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52839 q = 1) (hb : d238105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52839, d238105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52839, d238105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52840 q = 1) (hb : d238106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52840, d238106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52840, d238106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52841 q = 1) (hb : d238107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52841, d238107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52841, d238107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52842 q = 1) (hb : d238108 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52842, d238108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52842, d238108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52844 q = 1) (hb : d238110 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52844, d238110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73609 q ha hb
    | true =>
      simp only [d52844, d238110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52845 q = 1) (hb : d238111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52845, d238111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52845, d238111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52846 q = 1) (hb : d238112 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52846, d238112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52846, d238112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52847 q = 1) (hb : d238113 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52847, d238113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52847, d238113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52848 q = 1) (hb : d238114 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52848, d238114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52848, d238114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52849 q = 1) (hb : d238115 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52849, d238115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52849, d238115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73613 (p : Pattern) (ha : d52858 p = 1) (hb : d238124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52844 q = 1) (hb : d238110 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52844, d238110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73609 q ha hb
    | true =>
      simp only [d52844, d238110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52845 q = 1) (hb : d238111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52845, d238111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52845, d238111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52846 q = 1) (hb : d238112 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52846, d238112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52846, d238112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52847 q = 1) (hb : d238113 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52847, d238113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52847, d238113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52848 q = 1) (hb : d238114 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52848, d238114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52848, d238114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52858 q = 1) (hb : d238124 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52858, d238124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52858, d238124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73614 (p : Pattern) (ha : d52889 p = 1) (hb : d238146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23534 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
  have h2 (q : Pattern) (ha : d23422 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
    | true =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23535 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23535, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23423 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23536 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23536, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23537 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23537, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52879 q = 1) (hb : d238136 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52879, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52879, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
  have h8 (q : Pattern) (ha : d52702 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
    | true =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52880 q = 1) (hb : d238137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52880, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52880, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52703 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d52881 q = 1) (hb : d238138 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52881, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52881, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52882 q = 1) (hb : d238139 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52882, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52882, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52883 q = 1) (hb : d238140 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52883, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52883, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d52888 q = 1) (hb : d238145 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52888, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52888, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52889 q = 1) (hb : d238146 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52889, d238146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52889, d238146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73615 (p : Pattern) (ha : d52899 p = 1) (hb : d238151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52879 q = 1) (hb : d238136 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52879, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52879, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
  have h2 (q : Pattern) (ha : d52702 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
    | true =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d52880 q = 1) (hb : d238137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52880, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52880, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52703 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52881 q = 1) (hb : d238138 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52881, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52881, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52882 q = 1) (hb : d238139 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52882, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52882, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52888 q = 1) (hb : d238145 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52888, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52888, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52898 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d52899 q = 1) (hb : d238151 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52899, d238151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52899, d238151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro73616 (p : Pattern) (ha : d52918 p = 1) (hb : d238170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52900 q = 1) (hb : d238152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52900, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73614 q ha hb
    | true =>
      simp only [d52900, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73615 q ha hb
  have h2 (q : Pattern) (ha : d52901 q = 1) (hb : d238153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52901, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52901, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52902 q = 1) (hb : d238154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52902, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52902, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52908 q = 1) (hb : d238160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52908, d238160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52908, d238160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52917 q = 1) (hb : d238169 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52917, d238169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52917, d238169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52918 q = 1) (hb : d238170 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52918, d238170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52918, d238170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73617 (p : Pattern) (ha : d52929 p = 1) (hb : d238193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52919 q = 1) (hb : d238171 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52919, d238171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73616 q ha hb
    | true =>
      simp only [d52919, d238171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52920 q = 1) (hb : d238172 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52920, d238172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52920, d238172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52926 q = 1) (hb : d238190 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52926, d238190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52926, d238190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52927 q = 1) (hb : d238191 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52927, d238191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52927, d238191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52928 q = 1) (hb : d238192 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52928, d238192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52928, d238192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52929 q = 1) (hb : d238193 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52929, d238193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52929, d238193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73618 (p : Pattern) (ha : d52944 p = 1) (hb : d238199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52939 q = 1) (hb : d238194 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52939, d238194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73617 q ha hb
    | true =>
      simp only [d52939, d238194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52940 q = 1) (hb : d238195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52940, d238195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52940, d238195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52941 q = 1) (hb : d238196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52941, d238196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52941, d238196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52942 q = 1) (hb : d238197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52942, d238197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52942, d238197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52943 q = 1) (hb : d238198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52943, d238198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52943, d238198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52944 q = 1) (hb : d238199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52944, d238199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52944, d238199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73619 (p : Pattern) (ha : d52764 p = 1) (hb : d238035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52730 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73603 q ha hb
    | true =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52731 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52736 q = 1) (hb : d238007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52737 q = 1) (hb : d238008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52737, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52737, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52763 q = 1) (hb : d238034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52763, d238034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52763, d238034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52764 q = 1) (hb : d238035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52764, d238035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52764, d238035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73620 (p : Pattern) (ha : d52766 p = 1) (hb : d238037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d238011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52741 q = 1) (hb : d238012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52741, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52741, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52765 q = 1) (hb : d238036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52765, d238036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52765, d238036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52766 q = 1) (hb : d238037 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52766, d238037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52766, d238037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73621 (p : Pattern) (ha : d52773 p = 1) (hb : d238044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52730 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73603 q ha hb
    | true =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52731 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52736 q = 1) (hb : d238007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52771 q = 1) (hb : d238042 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52771, d238042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52771, d238042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52772 q = 1) (hb : d238043 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52772, d238043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52772, d238043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52773 q = 1) (hb : d238044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52773, d238044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52773, d238044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73622 (p : Pattern) (ha : d52776 p = 1) (hb : d238047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d238011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52774 q = 1) (hb : d238045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52774, d238045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52774, d238045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52775 q = 1) (hb : d238046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52775, d238046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52775, d238046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52776 q = 1) (hb : d238047 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52776, d238047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52776, d238047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73623 (p : Pattern) (ha : d52790 p = 1) (hb : d238051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d822 q = 1) (hb : d52499 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro120 q ha hb
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d823 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1202 q = 1) (hb : d52783 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1202, d52783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1202, d52783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52787 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d24014 q = 1) (hb : d52788 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24014, d52788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24014, d52788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d24015 q = 1) (hb : d52789 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24015, d52789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24015, d52789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52668 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d531 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d531, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d532 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d532, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d824 q = 1) (hb : d52671 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d824, d52671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52507 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d23692 q = 1) (hb : d52672 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23692, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23692, d52672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d23693 q = 1) (hb : d52673 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23693, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23693, d52673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52790 q = 1) (hb : d238051 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d52790, d238051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52790, d238051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro73624 (p : Pattern) (ha : d52796 p = 1) (hb : d238057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52791 q = 1) (hb : d238052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52791, d238052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73623 q ha hb
    | true =>
      simp only [d52791, d238052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52792 q = 1) (hb : d238053 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52792, d238053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52792, d238053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d52793 q = 1) (hb : d238054 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52793, d238054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52793, d238054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52794 q = 1) (hb : d238055 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52794, d238055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52794, d238055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d23695 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73598 q ha hb
    | true =>
      simp only [d23695, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23696 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23696, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23697 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23697, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23697, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23698 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23698, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23698, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d52795 q = 1) (hb : d238056 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52795, d238056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52795, d238056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d23422 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
    | true =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23423 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23424 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23425 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23425, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23699 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23699, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23699, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52796 q = 1) (hb : d238057 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52796, d238057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52796, d238057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro73625 (p : Pattern) (ha : d52802 p = 1) (hb : d238063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52797 q = 1) (hb : d238058 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52797, d238058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73624 q ha hb
    | true =>
      simp only [d52797, d238058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73600 q ha hb
  have h2 (q : Pattern) (ha : d52798 q = 1) (hb : d238059 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52798, d238059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52798, d238059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52799 q = 1) (hb : d238060 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52799, d238060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52799, d238060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52710 q = 1) (hb : d237990 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52710, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73600 q ha hb
    | true =>
      simp only [d52710, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73601 q ha hb
  have h5 (q : Pattern) (ha : d52711 q = 1) (hb : d237991 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52711, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52711, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52712 q = 1) (hb : d237992 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52712, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52712, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52800 q = 1) (hb : d238061 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52800, d238061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52800, d238061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52723 q = 1) (hb : d237994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52723, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73601 q ha hb
    | true =>
      simp only [d52723, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73602 q ha hb
  have h9 (q : Pattern) (ha : d52724 q = 1) (hb : d237995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52724, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52724, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52725 q = 1) (hb : d237996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52725, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52725, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52726 q = 1) (hb : d237997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52726, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52726, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52801 q = 1) (hb : d238062 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52801, d238062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52801, d238062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52802 q = 1) (hb : d238063 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52802, d238063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52802, d238063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73626 (p : Pattern) (ha : d52808 p = 1) (hb : d238069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52803 q = 1) (hb : d238064 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52803, d238064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73625 q ha hb
    | true =>
      simp only [d52803, d238064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52804 q = 1) (hb : d238065 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52804, d238065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52804, d238065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52730 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73603 q ha hb
    | true =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52731 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52805 q = 1) (hb : d238066 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52805, d238066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52805, d238066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52806 q = 1) (hb : d238067 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52806, d238067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52806, d238067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52807 q = 1) (hb : d238068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52807, d238068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52807, d238068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52808 q = 1) (hb : d238069 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52808, d238069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52808, d238069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73627 (p : Pattern) (ha : d74271 p = 1) (hb : d237989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
    | true =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d52702 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
    | true =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52703 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52704 q = 1) (hb : d237984 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52704, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52704, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52705 q = 1) (hb : d237985 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52705, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52705, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52706 q = 1) (hb : d237986 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52706, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52706, d237986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74266 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74266, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70728 q ha hb
    | true =>
      simp only [d74266, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d74267 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74267, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74267, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74268 q = 1) (hb : d237984 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74268, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74268, d237984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74269 q = 1) (hb : d237985 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74269, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74269, d237985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d74270 q = 1) (hb : d237988 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74270, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74270, d237988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74271 q = 1) (hb : d237989 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74271, d237989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74271, d237989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73628 (p : Pattern) (ha : d74278 p = 1) (hb : d238000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52710 q = 1) (hb : d237990 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52710, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73600 q ha hb
    | true =>
      simp only [d52710, d237990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73601 q ha hb
  have h2 (q : Pattern) (ha : d52711 q = 1) (hb : d237991 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52711, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52711, d237991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52712 q = 1) (hb : d237992 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52712, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52712, d237992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52723 q = 1) (hb : d237994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52723, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73601 q ha hb
    | true =>
      simp only [d52723, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73602 q ha hb
  have h5 (q : Pattern) (ha : d52724 q = 1) (hb : d237995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52724, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52724, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52725 q = 1) (hb : d237996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52725, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52725, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52726 q = 1) (hb : d237997 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52726, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52726, d237997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74273 q = 1) (hb : d237994 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d74273, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73627 q ha hb
    | true =>
      simp only [d74273, d237994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70729 q ha hb
  have h9 (q : Pattern) (ha : d74274 q = 1) (hb : d237995 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d74274, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74274, d237995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74275 q = 1) (hb : d237996 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74275, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74275, d237996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74276 q = 1) (hb : d237998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d74276, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74276, d237998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74277 q = 1) (hb : d237999 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d74277, d237999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74277, d237999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74278 q = 1) (hb : d238000 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d74278, d238000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74278, d238000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73629 (p : Pattern) (ha : d74284 p = 1) (hb : d238075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74279 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74279, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73628 q ha hb
    | true =>
      simp only [d74279, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74280 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74280, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74280, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74281 q = 1) (hb : d238072 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74281, d238072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74281, d238072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74282 q = 1) (hb : d238073 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74282, d238073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74282, d238073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74283 q = 1) (hb : d238074 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74283, d238074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74283, d238074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74284 q = 1) (hb : d238075 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74284, d238075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74284, d238075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73630 (p : Pattern) (ha : d74290 p = 1) (hb : d238081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52767 q = 1) (hb : d238038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52767, d238038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73619 q ha hb
    | true =>
      simp only [d52767, d238038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73620 q ha hb
  have h2 (q : Pattern) (ha : d52768 q = 1) (hb : d238039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52768, d238039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52768, d238039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52769 q = 1) (hb : d238040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52769, d238040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52769, d238040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52770 q = 1) (hb : d238041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52770, d238041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52770, d238041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52777 q = 1) (hb : d238048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52777, d238048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73621 q ha hb
    | true =>
      simp only [d52777, d238048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73622 q ha hb
  have h6 (q : Pattern) (ha : d52778 q = 1) (hb : d238049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52778, d238049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52778, d238049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52779 q = 1) (hb : d238050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52779, d238050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52779, d238050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52809 q = 1) (hb : d238070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52809, d238070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73626 q ha hb
    | true =>
      simp only [d52809, d238070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73605 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52810 q = 1) (hb : d238071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d238071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52810, d238071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d74285 q = 1) (hb : d238076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74285, d238076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73629 q ha hb
    | true =>
      simp only [d74285, d238076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74286 q = 1) (hb : d238077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74286, d238077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74286, d238077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d74287 q = 1) (hb : d238078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74287, d238078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74287, d238078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74288 q = 1) (hb : d238079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74288, d238079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74288, d238079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74289 q = 1) (hb : d238080 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74289, d238080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74289, d238080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74290 q = 1) (hb : d238081 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74290, d238081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74290, d238081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro73631 (p : Pattern) (ha : d52817 p = 1) (hb : d238082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52730 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73603 q ha hb
    | true =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52731 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52736 q = 1) (hb : d238007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52737 q = 1) (hb : d238008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52737, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52737, d238008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52763 q = 1) (hb : d238034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52763, d238034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52763, d238034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52817 q = 1) (hb : d238082 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52817, d238082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52817, d238082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73632 (p : Pattern) (ha : d52818 p = 1) (hb : d238083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d238011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52741 q = 1) (hb : d238012 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52741, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52741, d238012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52765 q = 1) (hb : d238036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52765, d238036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52765, d238036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52818 q = 1) (hb : d238083 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52818, d238083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52818, d238083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73633 (p : Pattern) (ha : d52823 p = 1) (hb : d238088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52730 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73603 q ha hb
    | true =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52731 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52736 q = 1) (hb : d238007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52736, d238007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52771 q = 1) (hb : d238042 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52771, d238042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52771, d238042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52772 q = 1) (hb : d238043 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52772, d238043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52772, d238043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52823 q = 1) (hb : d238088 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52823, d238088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52823, d238088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73634 (p : Pattern) (ha : d52824 p = 1) (hb : d238089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d238005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73604 q ha hb
    | true =>
      simp only [d52734, d238005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d238006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d238006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d238011 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d238011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52774 q = 1) (hb : d238045 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52774, d238045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52774, d238045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52775 q = 1) (hb : d238046 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52775, d238046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52775, d238046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52824 q = 1) (hb : d238089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52824, d238089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52824, d238089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73635 (p : Pattern) (ha : d52828 p = 1) (hb : d238093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52803 q = 1) (hb : d238064 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52803, d238064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73625 q ha hb
    | true =>
      simp only [d52803, d238064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52804 q = 1) (hb : d238065 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52804, d238065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52804, d238065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52730 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73603 q ha hb
    | true =>
      simp only [d52730, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52731 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52731, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52805 q = 1) (hb : d238066 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52805, d238066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52805, d238066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52806 q = 1) (hb : d238067 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52806, d238067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52806, d238067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52807 q = 1) (hb : d238068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52807, d238068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52807, d238068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52828 q = 1) (hb : d238093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52828, d238093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52828, d238093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73636 (p : Pattern) (ha : d74291 p = 1) (hb : d238096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74279 q = 1) (hb : d238001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74279, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73628 q ha hb
    | true =>
      simp only [d74279, d238001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74280 q = 1) (hb : d238002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74280, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74280, d238002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74281 q = 1) (hb : d238072 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74281, d238072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74281, d238072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74282 q = 1) (hb : d238073 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74282, d238073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74282, d238073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74283 q = 1) (hb : d238074 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74283, d238074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74283, d238074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74291 q = 1) (hb : d238096 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74291, d238096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74291, d238096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73637 (p : Pattern) (ha : d74297 p = 1) (hb : d238102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52767 q = 1) (hb : d238038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52767, d238038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73619 q ha hb
    | true =>
      simp only [d52767, d238038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73620 q ha hb
  have h2 (q : Pattern) (ha : d52768 q = 1) (hb : d238039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52768, d238039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52768, d238039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52769 q = 1) (hb : d238040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52769, d238040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52769, d238040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52770 q = 1) (hb : d238041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52770, d238041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52770, d238041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52777 q = 1) (hb : d238048 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52777, d238048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73621 q ha hb
    | true =>
      simp only [d52777, d238048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73622 q ha hb
  have h6 (q : Pattern) (ha : d52778 q = 1) (hb : d238049 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52778, d238049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52778, d238049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52779 q = 1) (hb : d238050 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52779, d238050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52779, d238050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52809 q = 1) (hb : d238070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52809, d238070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73626 q ha hb
    | true =>
      simp only [d52809, d238070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73605 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52810 q = 1) (hb : d238071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d238071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52810, d238071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d74285 q = 1) (hb : d238076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74285, d238076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73629 q ha hb
    | true =>
      simp only [d74285, d238076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74286 q = 1) (hb : d238077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74286, d238077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74286, d238077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d74287 q = 1) (hb : d238078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74287, d238078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74287, d238078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74288 q = 1) (hb : d238079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74288, d238079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74288, d238079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74289 q = 1) (hb : d238080 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74289, d238080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74289, d238080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d52819 q = 1) (hb : d238084 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52819, d238084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73631 q ha hb
    | true =>
      simp only [d52819, d238084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73632 q ha hb
  have h17 (q : Pattern) (ha : d52820 q = 1) (hb : d238085 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52820, d238085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52820, d238085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d52821 q = 1) (hb : d238086 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52821, d238086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d52821, d238086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d52822 q = 1) (hb : d238087 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52822, d238087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52822, d238087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d52825 q = 1) (hb : d238090 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52825, d238090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73633 q ha hb
    | true =>
      simp only [d52825, d238090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73634 q ha hb
  have h21 (q : Pattern) (ha : d52826 q = 1) (hb : d238091 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52826, d238091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52826, d238091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d52827 q = 1) (hb : d238092 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52827, d238092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d52827, d238092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d52829 q = 1) (hb : d238094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52829, d238094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73635 q ha hb
    | true =>
      simp only [d52829, d238094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73608 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d52830 q = 1) (hb : d238095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d238095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d52830, d238095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d74292 q = 1) (hb : d238097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74292, d238097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73636 q ha hb
    | true =>
      simp only [d74292, d238097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d74293 q = 1) (hb : d238098 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74293, d238098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d74293, d238098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d74294 q = 1) (hb : d238099 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74294, d238099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74294, d238099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74295 q = 1) (hb : d238100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74295, d238100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74295, d238100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74296 q = 1) (hb : d238101 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74296, d238101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74296, d238101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74297 q = 1) (hb : d238102 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74297, d238102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74297, d238102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro73638 (p : Pattern) (ha : d74304 p = 1) (hb : d238122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52829 q = 1) (hb : d238094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52829, d238094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73635 q ha hb
    | true =>
      simp only [d52829, d238094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73608 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52830 q = 1) (hb : d238095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d238095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52830, d238095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d74292 q = 1) (hb : d238097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74292, d238097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73636 q ha hb
    | true =>
      simp only [d74292, d238097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74293 q = 1) (hb : d238098 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74293, d238098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74293, d238098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74294 q = 1) (hb : d238099 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74294, d238099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74294, d238099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74302 q = 1) (hb : d238120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74302, d238120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74302, d238120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74303 q = 1) (hb : d238121 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74303, d238121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74303, d238121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74304 q = 1) (hb : d238122 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74304, d238122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74304, d238122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro73639 (p : Pattern) (ha : d52878 p = 1) (hb : d238135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52864 q = 1) (hb : d238130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52864, d238130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52864, d238130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73623 q ha hb
  have h2 (q : Pattern) (ha : d52791 q = 1) (hb : d238052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52791, d238052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73623 q ha hb
    | true =>
      simp only [d52791, d238052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d52865 q = 1) (hb : d238131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52865, d238131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52865, d238131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52792 q = 1) (hb : d238053 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52792, d238053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52792, d238053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52866 q = 1) (hb : d238132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52866, d238132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52866, d238132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52867 q = 1) (hb : d238133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52867, d238133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52867, d238133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d23814 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23814, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23814, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73598 q ha hb
  have h8 (q : Pattern) (ha : d23695 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73598 q ha hb
    | true =>
      simp only [d23695, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23815 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23815, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23815, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23696 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23696, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23816 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23816, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23816, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23817 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23817, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23817, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d52872 q = 1) (hb : d238134 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52872, d238134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52872, d238134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d23534 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
  have h15 (q : Pattern) (ha : d23422 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
    | true =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23535 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23535, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23423 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23536 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23536, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23537 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23537, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23818 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23818, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23818, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d52878 q = 1) (hb : d238135 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52878, d238135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52878, d238135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro73640 (p : Pattern) (ha : d52884 p = 1) (hb : d238141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23814 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23814, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23814, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73598 q ha hb
  have h2 (q : Pattern) (ha : d23695 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73598 q ha hb
    | true =>
      simp only [d23695, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23815 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23815, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23815, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23696 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23696, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23816 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23816, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23816, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23817 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23817, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23817, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23534 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
  have h8 (q : Pattern) (ha : d23422 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
    | true =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d23535 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23535, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23423 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23536 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23536, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23537 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23537, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d23818 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23818, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23818, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d52879 q = 1) (hb : d238136 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52879, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52879, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
  have h15 (q : Pattern) (ha : d52702 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
    | true =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d52880 q = 1) (hb : d238137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52880, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d52880, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d52703 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d52881 q = 1) (hb : d238138 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52881, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52881, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d52882 q = 1) (hb : d238139 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52882, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d52882, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d52883 q = 1) (hb : d238140 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52883, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d52883, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d52884 q = 1) (hb : d238141 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52884, d238141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d52884, d238141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73641 (p : Pattern) (ha : d52905 p = 1) (hb : d238157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52885 q = 1) (hb : d238142 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52885, d238142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73639 q ha hb
    | true =>
      simp only [d52885, d238142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73640 q ha hb
  have h2 (q : Pattern) (ha : d52886 q = 1) (hb : d238143 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52886, d238143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52886, d238143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52887 q = 1) (hb : d238144 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52887, d238144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52887, d238144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52890 q = 1) (hb : d238147 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52890, d238147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73640 q ha hb
    | true =>
      simp only [d52890, d238147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73614 q ha hb
  have h5 (q : Pattern) (ha : d52891 q = 1) (hb : d238148 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52891, d238148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52891, d238148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52892 q = 1) (hb : d238149 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52892, d238149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52892, d238149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52893 q = 1) (hb : d238150 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52893, d238150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52893, d238150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52900 q = 1) (hb : d238152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52900, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73614 q ha hb
    | true =>
      simp only [d52900, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73615 q ha hb
  have h9 (q : Pattern) (ha : d52901 q = 1) (hb : d238153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52901, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52901, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52902 q = 1) (hb : d238154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52902, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52902, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52903 q = 1) (hb : d238155 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52903, d238155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52903, d238155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52904 q = 1) (hb : d238156 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52904, d238156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52904, d238156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52905 q = 1) (hb : d238157 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52905, d238157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52905, d238157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73642 (p : Pattern) (ha : d52910 p = 1) (hb : d238162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52890 q = 1) (hb : d238147 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52890, d238147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73640 q ha hb
    | true =>
      simp only [d52890, d238147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73614 q ha hb
  have h2 (q : Pattern) (ha : d52891 q = 1) (hb : d238148 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52891, d238148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52891, d238148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52892 q = 1) (hb : d238149 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52892, d238149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52892, d238149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52900 q = 1) (hb : d238152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52900, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73614 q ha hb
    | true =>
      simp only [d52900, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73615 q ha hb
  have h5 (q : Pattern) (ha : d52901 q = 1) (hb : d238153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52901, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52901, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52902 q = 1) (hb : d238154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52902, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52902, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52903 q = 1) (hb : d238155 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52903, d238155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52903, d238155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52908 q = 1) (hb : d238160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52908, d238160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52908, d238160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52909 q = 1) (hb : d238161 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52909, d238161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52909, d238161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52910 q = 1) (hb : d238162 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52910, d238162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52910, d238162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro73643 (p : Pattern) (ha : d52916 p = 1) (hb : d238168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52906 q = 1) (hb : d238158 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52906, d238158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73641 q ha hb
    | true =>
      simp only [d52906, d238158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52907 q = 1) (hb : d238159 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52907, d238159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52907, d238159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52911 q = 1) (hb : d238163 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52911, d238163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73642 q ha hb
    | true =>
      simp only [d52911, d238163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52912 q = 1) (hb : d238164 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52912, d238164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52912, d238164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52913 q = 1) (hb : d238165 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52913, d238165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52913, d238165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52914 q = 1) (hb : d238166 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52914, d238166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52914, d238166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52915 q = 1) (hb : d238167 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52915, d238167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52915, d238167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52916 q = 1) (hb : d238168 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52916, d238168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52916, d238168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73644 (p : Pattern) (ha : d52924 p = 1) (hb : d238176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52911 q = 1) (hb : d238163 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52911, d238163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73642 q ha hb
    | true =>
      simp only [d52911, d238163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52912 q = 1) (hb : d238164 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52912, d238164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52912, d238164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52919 q = 1) (hb : d238171 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52919, d238171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73616 q ha hb
    | true =>
      simp only [d52919, d238171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52920 q = 1) (hb : d238172 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52920, d238172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52920, d238172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52921 q = 1) (hb : d238173 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52921, d238173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52921, d238173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52922 q = 1) (hb : d238174 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52922, d238174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52922, d238174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52923 q = 1) (hb : d238175 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52923, d238175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52923, d238175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52924 q = 1) (hb : d238176 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52924, d238176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52924, d238176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73645 (p : Pattern) (ha : d74315 p = 1) (hb : d238146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23534 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
  have h2 (q : Pattern) (ha : d23422 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73597 q ha hb
    | true =>
      simp only [d23422, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23535 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23535, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23423 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23423, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23536 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23536, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23537 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23537, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d52879 q = 1) (hb : d238136 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52879, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52879, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
  have h8 (q : Pattern) (ha : d52702 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73599 q ha hb
    | true =>
      simp only [d52702, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52880 q = 1) (hb : d238137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52880, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52880, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52703 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52703, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d52881 q = 1) (hb : d238138 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52881, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52881, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52882 q = 1) (hb : d238139 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52882, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52882, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52883 q = 1) (hb : d238140 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52883, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52883, d238140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74310 q = 1) (hb : d238136 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74310, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74310, d238136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70728 q ha hb
  have h15 (q : Pattern) (ha : d74266 q = 1) (hb : d237982 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74266, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70728 q ha hb
    | true =>
      simp only [d74266, d237982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74311 q = 1) (hb : d238137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74311, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74311, d238137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74267 q = 1) (hb : d237983 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74267, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74267, d237983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d74312 q = 1) (hb : d238138 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74312, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74312, d238138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d74313 q = 1) (hb : d238139 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74313, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74313, d238139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d74314 q = 1) (hb : d238145 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74314, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74314, d238145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74315 q = 1) (hb : d238146 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74315, d238146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74315, d238146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73646 (p : Pattern) (ha : d74322 p = 1) (hb : d238162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52890 q = 1) (hb : d238147 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52890, d238147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73640 q ha hb
    | true =>
      simp only [d52890, d238147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73614 q ha hb
  have h2 (q : Pattern) (ha : d52891 q = 1) (hb : d238148 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52891, d238148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52891, d238148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52892 q = 1) (hb : d238149 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52892, d238149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52892, d238149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52900 q = 1) (hb : d238152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52900, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73614 q ha hb
    | true =>
      simp only [d52900, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73615 q ha hb
  have h5 (q : Pattern) (ha : d52901 q = 1) (hb : d238153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52901, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52901, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52902 q = 1) (hb : d238154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52902, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52902, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52903 q = 1) (hb : d238155 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52903, d238155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52903, d238155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74317 q = 1) (hb : d238152 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d74317, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73645 q ha hb
    | true =>
      simp only [d74317, d238152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70754 q ha hb
  have h9 (q : Pattern) (ha : d74318 q = 1) (hb : d238153 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d74318, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74318, d238153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74319 q = 1) (hb : d238154 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74319, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74319, d238154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74320 q = 1) (hb : d238160 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d74320, d238160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74320, d238160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74321 q = 1) (hb : d238161 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d74321, d238161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74321, d238161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74322 q = 1) (hb : d238162 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d74322, d238162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74322, d238162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73647 (p : Pattern) (ha : d74328 p = 1) (hb : d238182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74323 q = 1) (hb : d238163 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74323, d238163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73646 q ha hb
    | true =>
      simp only [d74323, d238163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74324 q = 1) (hb : d238164 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74324, d238164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74324, d238164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74325 q = 1) (hb : d238179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74325, d238179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74325, d238179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74326 q = 1) (hb : d238180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74326, d238180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74326, d238180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74327 q = 1) (hb : d238181 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74327, d238181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74327, d238181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74328 q = 1) (hb : d238182 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74328, d238182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74328, d238182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73648 (p : Pattern) (ha : d74334 p = 1) (hb : d238188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52925 q = 1) (hb : d238177 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52925, d238177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73643 q ha hb
    | true =>
      simp only [d52925, d238177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73644 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52930 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52931 q = 1) (hb : d238178 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d238178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52931, d238178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d74329 q = 1) (hb : d238183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74329, d238183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73647 q ha hb
    | true =>
      simp only [d74329, d238183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74330 q = 1) (hb : d238184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74330, d238184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74330, d238184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74331 q = 1) (hb : d238185 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74331, d238185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74331, d238185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74332 q = 1) (hb : d238186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74332, d238186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74332, d238186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74333 q = 1) (hb : d238187 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74333, d238187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74333, d238187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74334 q = 1) (hb : d238188 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74334, d238188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74334, d238188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro73649 (p : Pattern) (ha : d74340 p = 1) (hb : d238205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52750 q = 1) (hb : d238021 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52750, d238021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52750, d238021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73607 q ha hb
  have h2 (q : Pattern) (ha : d52751 q = 1) (hb : d238022 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52751, d238022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d52751, d238022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d52760 q = 1) (hb : d238031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52760, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73607 q ha hb
    | true =>
      simp only [d52760, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73610 q ha hb
  have h4 (q : Pattern) (ha : d52761 q = 1) (hb : d238032 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52761, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52761, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52762 q = 1) (hb : d238033 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52762, d238033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52762, d238033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74298 q = 1) (hb : d238103 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74298, d238103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73630 q ha hb
    | true =>
      simp only [d74298, d238103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73637 q ha hb
  have h7 (q : Pattern) (ha : d52850 q = 1) (hb : d238116 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52850, d238116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73611 q ha hb
    | true =>
      simp only [d52850, d238116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73612 q ha hb
  have h8 (q : Pattern) (ha : d74299 q = 1) (hb : d238117 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74299, d238117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74299, d238117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74300 q = 1) (hb : d238118 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74300, d238118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74300, d238118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74301 q = 1) (hb : d238119 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74301, d238119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74301, d238119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74305 q = 1) (hb : d238123 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74305, d238123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74305, d238123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73638 q ha hb
  have h12 (q : Pattern) (ha : d52859 q = 1) (hb : d238125 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52859, d238125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52859, d238125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73613 q ha hb
  have h13 (q : Pattern) (ha : d74306 q = 1) (hb : d238126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74306, d238126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74306, d238126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74307 q = 1) (hb : d238127 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74307, d238127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74307, d238127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74308 q = 1) (hb : d238128 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74308, d238128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74308, d238128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74309 q = 1) (hb : d238129 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74309, d238129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74309, d238129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74335 q = 1) (hb : d238189 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74335, d238189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74335, d238189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73648 q ha hb
  have h18 (q : Pattern) (ha : d52945 q = 1) (hb : d238200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52945, d238200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52945, d238200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73618 q ha hb
  have h19 (q : Pattern) (ha : d74336 q = 1) (hb : d238201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74336, d238201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74336, d238201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74337 q = 1) (hb : d238202 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74337, d238202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74337, d238202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74338 q = 1) (hb : d238203 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74338, d238203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74338, d238203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74339 q = 1) (hb : d238204 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74339, d238204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74339, d238204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74340 q = 1) (hb : d238205 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74340, d238205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74340, d238205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro73650 (p : Pattern) (ha : d74346 p = 1) (hb : d238211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74341 q = 1) (hb : d238206 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74341, d238206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74341, d238206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73649 q ha hb
  have h2 (q : Pattern) (ha : d74342 q = 1) (hb : d238207 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74342, d238207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74342, d238207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74343 q = 1) (hb : d238208 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74343, d238208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74343, d238208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74344 q = 1) (hb : d238209 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74344, d238209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74344, d238209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74345 q = 1) (hb : d238210 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74345, d238210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74345, d238210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74346 q = 1) (hb : d238211 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74346, d238211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74346, d238211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73651 (p : Pattern) (ha : d29557 p = 1) (hb : d53010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52967 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d29527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d29528 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29528, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29528, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52983 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d29532 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d29533 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29533, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29534 q = 1) (hb : d52987 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29534, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29534, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52992 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d29555 q = 1) (hb : d52993 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29555, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29555, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d29556 q = 1) (hb : d52994 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29556, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29556, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1549 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1550 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1550, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29546 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29546, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29546, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d29547 q = 1) (hb : d53008 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29547, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d29547, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d29548 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29548, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d29548, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h21 (q : Pattern) (ha : d29557 q = 1) (hb : d53010 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29557, d53010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29557, d53010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73652 (p : Pattern) (ha : d29664 p = 1) (hb : d52995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52967 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d29527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d29527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d29528 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29528, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29528, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29529 q = 1) (hb : d52971 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29529, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29529, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52977 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d29530 q = 1) (hb : d52978 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29530, d52978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29530, d52978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29531 q = 1) (hb : d52979 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29531, d52979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29531, d52979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52983 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d29532 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d29533 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29533, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29534 q = 1) (hb : d52987 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29534, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29534, d52987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52992 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d29555 q = 1) (hb : d52993 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29555, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29555, d52993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d29556 q = 1) (hb : d52994 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29556, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d29556, d52994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d29664 q = 1) (hb : d52995 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29664, d52995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29664, d52995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73653 (p : Pattern) (ha : d53022 p = 1) (hb : d238217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29532 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d29533 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29533, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1549 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1550 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1550, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29546 q = 1) (hb : d53003 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29546, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29546, d53003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d29547 q = 1) (hb : d53008 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29547, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29547, d53008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d29548 q = 1) (hb : d53009 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29548, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29548, d53009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53017 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h15 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h16 (q : Pattern) (ha : d29564 q = 1) (hb : d53018 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29564, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29564, d53018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d53020 q = 1) (hb : d238215 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d53020, d238215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d53020, d238215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d53021 q = 1) (hb : d238216 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d53021, d238216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53021, d238216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h20 (q : Pattern) (ha : d53022 q = 1) (hb : d238217 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d53022, d238217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d53022, d238217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro73654 (p : Pattern) (ha : d53028 p = 1) (hb : d238223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29665 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29665, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73652 q ha hb
    | true =>
      simp only [d29665, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29666 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29666, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29666, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29667 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29667, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29667, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29668 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29668, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29668, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29558 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
    | true =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29559 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29560 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29560, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29560, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29561 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29561, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29561, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29670 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29670, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29670, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53023 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
    | true =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53024 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d53025 q = 1) (hb : d238220 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53025, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53025, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53026 q = 1) (hb : d238221 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53026, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53026, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d53027 q = 1) (hb : d238222 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53027, d238222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53027, d238222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53028 q = 1) (hb : d238223 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53028, d238223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53028, d238223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73655 (p : Pattern) (ha : d53030 p = 1) (hb : d238225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29558 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
    | true =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29559 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29560 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29560, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29560, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29561 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29561, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29561, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53023 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
    | true =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53024 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53025 q = 1) (hb : d238220 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53025, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53025, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53026 q = 1) (hb : d238221 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53026, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53026, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53027 q = 1) (hb : d238222 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53027, d238222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53027, d238222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53029 q = 1) (hb : d238224 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53029, d238224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53029, d238224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53030 q = 1) (hb : d238225 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53030, d238225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53030, d238225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73656 (p : Pattern) (ha : d53043 p = 1) (hb : d238229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53023 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
    | true =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53024 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53025 q = 1) (hb : d238220 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53025, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53025, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53026 q = 1) (hb : d238221 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53026, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53026, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53029 q = 1) (hb : d238224 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53029, d238224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53029, d238224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53043 q = 1) (hb : d238229 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53043, d238229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53043, d238229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro73657 (p : Pattern) (ha : d53050 p = 1) (hb : d238236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53031 q = 1) (hb : d238226 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53031, d238226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73654 q ha hb
    | true =>
      simp only [d53031, d238226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73655 q ha hb
  have h2 (q : Pattern) (ha : d53032 q = 1) (hb : d238227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53032, d238227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53032, d238227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53033 q = 1) (hb : d238228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53033, d238228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53033, d238228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53044 q = 1) (hb : d238230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53044, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73655 q ha hb
    | true =>
      simp only [d53044, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73656 q ha hb
  have h5 (q : Pattern) (ha : d53045 q = 1) (hb : d238231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53045, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53045, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53046 q = 1) (hb : d238232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53046, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53046, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53047 q = 1) (hb : d238233 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53047, d238233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53047, d238233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53048 q = 1) (hb : d238234 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53048, d238234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53048, d238234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53049 q = 1) (hb : d238235 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53049, d238235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53049, d238235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53050 q = 1) (hb : d238236 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53050, d238236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53050, d238236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro73658 (p : Pattern) (ha : d53054 p = 1) (hb : d238240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53044 q = 1) (hb : d238230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53044, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73655 q ha hb
    | true =>
      simp only [d53044, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73656 q ha hb
  have h2 (q : Pattern) (ha : d53045 q = 1) (hb : d238231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53045, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53045, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53046 q = 1) (hb : d238232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53046, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53046, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53048 q = 1) (hb : d238234 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53048, d238234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53048, d238234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53053 q = 1) (hb : d238239 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53053, d238239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53053, d238239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53054 q = 1) (hb : d238240 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53054, d238240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53054, d238240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73659 (p : Pattern) (ha : d53060 p = 1) (hb : d238246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53051 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73657 q ha hb
    | true =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53052 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53057 q = 1) (hb : d238243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53058 q = 1) (hb : d238244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53058, d238244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53058, d238244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53059 q = 1) (hb : d238245 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53059, d238245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53059, d238245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53060 q = 1) (hb : d238246 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53060, d238246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53060, d238246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73660 (p : Pattern) (ha : d53064 p = 1) (hb : d238250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d238247 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53062 q = 1) (hb : d238248 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53062, d238248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53062, d238248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53063 q = 1) (hb : d238249 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53063, d238249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53063, d238249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53064 q = 1) (hb : d238250 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53064, d238250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53064, d238250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73661 (p : Pattern) (ha : d53070 p = 1) (hb : d238256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53065 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73659 q ha hb
    | true =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73660 q ha hb
  have h2 (q : Pattern) (ha : d53066 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53066, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53066, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53067 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53067, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53067, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53068 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53068, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53068, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53069 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53069, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53069, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53070 q = 1) (hb : d238256 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53070, d238256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53070, d238256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73662 (p : Pattern) (ha : d53073 p = 1) (hb : d238259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53051 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73657 q ha hb
    | true =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53052 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53057 q = 1) (hb : d238243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53058 q = 1) (hb : d238244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53058, d238244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53058, d238244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53059 q = 1) (hb : d238245 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53059, d238245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53059, d238245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53073 q = 1) (hb : d238259 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53073, d238259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53073, d238259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73663 (p : Pattern) (ha : d53074 p = 1) (hb : d238260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d238247 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53062 q = 1) (hb : d238248 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53062, d238248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53062, d238248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53063 q = 1) (hb : d238249 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53063, d238249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53063, d238249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53074 q = 1) (hb : d238260 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53074, d238260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53074, d238260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73664 (p : Pattern) (ha : d53080 p = 1) (hb : d238266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53065 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73659 q ha hb
    | true =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73660 q ha hb
  have h2 (q : Pattern) (ha : d53066 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53066, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53066, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53067 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53067, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53067, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53068 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53068, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53068, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53069 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53069, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53069, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53075 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53075, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73662 q ha hb
    | true =>
      simp only [d53075, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73663 q ha hb
  have h7 (q : Pattern) (ha : d53076 q = 1) (hb : d238262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53076, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53076, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53077 q = 1) (hb : d238263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53077, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53077, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53078 q = 1) (hb : d238264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53078, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53078, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53079 q = 1) (hb : d238265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53079, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53079, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53080 q = 1) (hb : d238266 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53080, d238266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53080, d238266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73665 (p : Pattern) (ha : d53158 p = 1) (hb : d238338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53065 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73659 q ha hb
    | true =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73660 q ha hb
  have h2 (q : Pattern) (ha : d53066 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53066, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53066, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53067 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53067, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53067, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53068 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53068, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53068, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53069 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53069, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53069, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53153 q = 1) (hb : d238333 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53153, d238333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73660 q ha hb
    | true =>
      simp only [d53153, d238333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53154 q = 1) (hb : d238334 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53154, d238334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53154, d238334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53155 q = 1) (hb : d238335 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53155, d238335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53155, d238335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53156 q = 1) (hb : d238336 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53156, d238336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53156, d238336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53157 q = 1) (hb : d238337 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53157, d238337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53157, d238337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53158 q = 1) (hb : d238338 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53158, d238338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53158, d238338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73666 (p : Pattern) (ha : d53164 p = 1) (hb : d238344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53153 q = 1) (hb : d238333 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53153, d238333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73660 q ha hb
    | true =>
      simp only [d53153, d238333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53154 q = 1) (hb : d238334 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53154, d238334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53154, d238334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53155 q = 1) (hb : d238335 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53155, d238335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53155, d238335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53156 q = 1) (hb : d238336 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53156, d238336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53156, d238336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53157 q = 1) (hb : d238337 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53157, d238337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53157, d238337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53159 q = 1) (hb : d238339 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53159, d238339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73663 q ha hb
    | true =>
      simp only [d53159, d238339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53160 q = 1) (hb : d238340 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53160, d238340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53160, d238340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53161 q = 1) (hb : d238341 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53161, d238341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53161, d238341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53162 q = 1) (hb : d238342 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53162, d238342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53162, d238342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53163 q = 1) (hb : d238343 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53163, d238343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53163, d238343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53164 q = 1) (hb : d238344 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53164, d238344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53164, d238344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73667 (p : Pattern) (ha : d53173 p = 1) (hb : d238353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53159 q = 1) (hb : d238339 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53159, d238339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73663 q ha hb
    | true =>
      simp only [d53159, d238339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53160 q = 1) (hb : d238340 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53160, d238340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53160, d238340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53161 q = 1) (hb : d238341 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53161, d238341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53161, d238341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53162 q = 1) (hb : d238342 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53162, d238342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53162, d238342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53163 q = 1) (hb : d238343 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53163, d238343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53163, d238343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53173 q = 1) (hb : d238353 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53173, d238353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53173, d238353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73668 (p : Pattern) (ha : d53204 p = 1) (hb : d238369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29881 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29881, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29881, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
  have h2 (q : Pattern) (ha : d29558 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
    | true =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29882 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29882, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29882, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29559 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29883 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29883, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29883, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29884 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29884, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29884, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53194 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53194, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53194, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
  have h8 (q : Pattern) (ha : d53023 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
    | true =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53195 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53195, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53195, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53024 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53196 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53196, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53196, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53197 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53197, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53197, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d53198 q = 1) (hb : d238363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53198, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53198, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53203 q = 1) (hb : d238368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53203, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53203, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d53204 q = 1) (hb : d238369 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53204, d238369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53204, d238369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73669 (p : Pattern) (ha : d53214 p = 1) (hb : d238374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53194 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53194, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53194, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
  have h2 (q : Pattern) (ha : d53023 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
    | true =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53195 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53195, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53195, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53024 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53196 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53196, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53196, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53197 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53197, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53197, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53203 q = 1) (hb : d238368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53203, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53203, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53213 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53214 q = 1) (hb : d238374 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53214, d238374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53214, d238374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro73670 (p : Pattern) (ha : d53233 p = 1) (hb : d238393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53215 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53215, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73668 q ha hb
    | true =>
      simp only [d53215, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73669 q ha hb
  have h2 (q : Pattern) (ha : d53216 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53216, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53216, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53217 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53217, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53217, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53223 q = 1) (hb : d238383 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53223, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53223, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53232 q = 1) (hb : d238392 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53232, d238392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53232, d238392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53233 q = 1) (hb : d238393 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53233, d238393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53233, d238393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73671 (p : Pattern) (ha : d53244 p = 1) (hb : d238416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53234 q = 1) (hb : d238394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53234, d238394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73670 q ha hb
    | true =>
      simp only [d53234, d238394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53235 q = 1) (hb : d238395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53235, d238395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53235, d238395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53241 q = 1) (hb : d238413 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53241, d238413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53241, d238413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53242 q = 1) (hb : d238414 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53242, d238414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53242, d238414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53243 q = 1) (hb : d238415 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53243, d238415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53243, d238415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53244 q = 1) (hb : d238416 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53244, d238416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53244, d238416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73672 (p : Pattern) (ha : d53259 p = 1) (hb : d238422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53254 q = 1) (hb : d238417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53254, d238417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73671 q ha hb
    | true =>
      simp only [d53254, d238417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53255 q = 1) (hb : d238418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53255, d238418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53255, d238418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53256 q = 1) (hb : d238419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53256, d238419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53256, d238419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53257 q = 1) (hb : d238420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53257, d238420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53257, d238420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53258 q = 1) (hb : d238421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53258, d238421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53258, d238421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53259 q = 1) (hb : d238422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53259, d238422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53259, d238422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73673 (p : Pattern) (ha : d53085 p = 1) (hb : d238271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53051 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73657 q ha hb
    | true =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53052 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53057 q = 1) (hb : d238243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53058 q = 1) (hb : d238244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53058, d238244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53058, d238244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53084 q = 1) (hb : d238270 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53084, d238270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53084, d238270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53085 q = 1) (hb : d238271 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53085, d238271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53085, d238271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73674 (p : Pattern) (ha : d53087 p = 1) (hb : d238273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d238247 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53062 q = 1) (hb : d238248 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53062, d238248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53062, d238248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53086 q = 1) (hb : d238272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53086, d238272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53086, d238272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53087 q = 1) (hb : d238273 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53087, d238273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53087, d238273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73675 (p : Pattern) (ha : d53094 p = 1) (hb : d238280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53051 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73657 q ha hb
    | true =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53052 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53057 q = 1) (hb : d238243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53092 q = 1) (hb : d238278 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53092, d238278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53092, d238278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53093 q = 1) (hb : d238279 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53093, d238279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53093, d238279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53094 q = 1) (hb : d238280 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53094, d238280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53094, d238280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73676 (p : Pattern) (ha : d53097 p = 1) (hb : d238283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d238247 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53095 q = 1) (hb : d238281 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53095, d238281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53095, d238281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53096 q = 1) (hb : d238282 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53096, d238282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53096, d238282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53097 q = 1) (hb : d238283 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53097, d238283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53097, d238283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73677 (p : Pattern) (ha : d29659 p = 1) (hb : d53105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1660 q = 1) (hb : d53101 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1660, d53101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1660, d53101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53102 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d24396 q = 1) (hb : d53103 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24396, d53103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d24396, d53103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d24397 q = 1) (hb : d53104 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24397, d53104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24397, d53104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52967 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d29527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d29527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d29528 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29528, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29528, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29529 q = 1) (hb : d52971 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29529, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29529, d52971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52977 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d29530 q = 1) (hb : d52978 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29530, d52978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29530, d52978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29531 q = 1) (hb : d52979 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29531, d52979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29531, d52979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29659 q = 1) (hb : d53105 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29659, d53105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29659, d53105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73678 (p : Pattern) (ha : d29671 p = 1) (hb : d53111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29660 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29660, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73677 q ha hb
    | true =>
      simp only [d29660, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29661 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29661, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29661, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29662 q = 1) (hb : d53108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29662, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29662, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29663 q = 1) (hb : d53109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29663, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29663, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29665 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29665, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73652 q ha hb
    | true =>
      simp only [d29665, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29666 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29666, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29666, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29667 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29667, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29667, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29668 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29668, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29668, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29669 q = 1) (hb : d53110 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29669, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29669, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29558 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
    | true =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29559 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29560 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29560, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29560, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29561 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29561, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29561, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29670 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29670, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29670, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29671 q = 1) (hb : d53111 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29671, d53111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29671, d53111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73679 (p : Pattern) (ha : d53117 p = 1) (hb : d238292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53112 q = 1) (hb : d238287 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53112, d238287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73678 q hb ha
    | true =>
      simp only [d53112, d238287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73654 q ha hb
  have h2 (q : Pattern) (ha : d53113 q = 1) (hb : d238288 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53113, d238288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53113, d238288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53114 q = 1) (hb : d238289 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53114, d238289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53114, d238289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53031 q = 1) (hb : d238226 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53031, d238226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73654 q ha hb
    | true =>
      simp only [d53031, d238226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73655 q ha hb
  have h5 (q : Pattern) (ha : d53032 q = 1) (hb : d238227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53032, d238227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53032, d238227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53033 q = 1) (hb : d238228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53033, d238228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53033, d238228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53115 q = 1) (hb : d238290 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53115, d238290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53115, d238290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53044 q = 1) (hb : d238230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53044, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73655 q ha hb
    | true =>
      simp only [d53044, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73656 q ha hb
  have h9 (q : Pattern) (ha : d53045 q = 1) (hb : d238231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53045, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53045, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53046 q = 1) (hb : d238232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53046, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53046, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53047 q = 1) (hb : d238233 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53047, d238233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53047, d238233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53116 q = 1) (hb : d238291 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53116, d238291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53116, d238291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53117 q = 1) (hb : d238292 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53117, d238292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53117, d238292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73680 (p : Pattern) (ha : d53123 p = 1) (hb : d238298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53118 q = 1) (hb : d238293 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53118, d238293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73679 q ha hb
    | true =>
      simp only [d53118, d238293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53119 q = 1) (hb : d238294 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53119, d238294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53119, d238294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53051 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73657 q ha hb
    | true =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53052 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53120 q = 1) (hb : d238295 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53120, d238295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53120, d238295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53121 q = 1) (hb : d238296 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53121, d238296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53121, d238296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53122 q = 1) (hb : d238297 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53122, d238297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53122, d238297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53123 q = 1) (hb : d238298 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53123, d238298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53123, d238298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73681 (p : Pattern) (ha : d74361 p = 1) (hb : d238225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29558 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
    | true =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29559 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29560 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29560, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29560, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29561 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29561, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29561, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53023 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
    | true =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53024 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53025 q = 1) (hb : d238220 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53025, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53025, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53026 q = 1) (hb : d238221 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53026, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53026, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53027 q = 1) (hb : d238222 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53027, d238222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53027, d238222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74356 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70785 q ha hb
    | true =>
      simp only [d74356, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d74357 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74357, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74358 q = 1) (hb : d238220 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74358, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74358, d238220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74359 q = 1) (hb : d238221 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74359, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74359, d238221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d74360 q = 1) (hb : d238224 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74360, d238224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74360, d238224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74361 q = 1) (hb : d238225 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74361, d238225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74361, d238225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73682 (p : Pattern) (ha : d74368 p = 1) (hb : d238236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53031 q = 1) (hb : d238226 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53031, d238226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73654 q ha hb
    | true =>
      simp only [d53031, d238226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73655 q ha hb
  have h2 (q : Pattern) (ha : d53032 q = 1) (hb : d238227 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53032, d238227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53032, d238227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53033 q = 1) (hb : d238228 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53033, d238228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53033, d238228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53044 q = 1) (hb : d238230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53044, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73655 q ha hb
    | true =>
      simp only [d53044, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73656 q ha hb
  have h5 (q : Pattern) (ha : d53045 q = 1) (hb : d238231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53045, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53045, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53046 q = 1) (hb : d238232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53046, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53046, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53047 q = 1) (hb : d238233 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53047, d238233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53047, d238233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74363 q = 1) (hb : d238230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d74363, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73681 q ha hb
    | true =>
      simp only [d74363, d238230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70786 q ha hb
  have h9 (q : Pattern) (ha : d74364 q = 1) (hb : d238231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d74364, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74364, d238231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74365 q = 1) (hb : d238232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74365, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74365, d238232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74366 q = 1) (hb : d238234 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d74366, d238234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74366, d238234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74367 q = 1) (hb : d238235 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d74367, d238235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74367, d238235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74368 q = 1) (hb : d238236 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d74368, d238236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74368, d238236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73683 (p : Pattern) (ha : d74374 p = 1) (hb : d238304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74369 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74369, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73682 q ha hb
    | true =>
      simp only [d74369, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74370 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74370, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74370, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74371 q = 1) (hb : d238301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74371, d238301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74371, d238301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74372 q = 1) (hb : d238302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74372, d238302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74372, d238302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74373 q = 1) (hb : d238303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74373, d238303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74373, d238303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74374 q = 1) (hb : d238304 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74374, d238304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74374, d238304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73684 (p : Pattern) (ha : d74380 p = 1) (hb : d238310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53088 q = 1) (hb : d238274 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53088, d238274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73673 q ha hb
    | true =>
      simp only [d53088, d238274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73674 q ha hb
  have h2 (q : Pattern) (ha : d53089 q = 1) (hb : d238275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53089, d238275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53089, d238275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53090 q = 1) (hb : d238276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53090, d238276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53090, d238276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53091 q = 1) (hb : d238277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53091, d238277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53091, d238277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53098 q = 1) (hb : d238284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53098, d238284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73675 q ha hb
    | true =>
      simp only [d53098, d238284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73676 q ha hb
  have h6 (q : Pattern) (ha : d53099 q = 1) (hb : d238285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53099, d238285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53099, d238285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53100 q = 1) (hb : d238286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53100, d238286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53100, d238286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53124 q = 1) (hb : d238299 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53124, d238299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73680 q ha hb
    | true =>
      simp only [d53124, d238299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73659 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53125 q = 1) (hb : d238300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d238300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53125, d238300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d74375 q = 1) (hb : d238305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74375, d238305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73683 q ha hb
    | true =>
      simp only [d74375, d238305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74376 q = 1) (hb : d238306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74376, d238306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74376, d238306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d74377 q = 1) (hb : d238307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74377, d238307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74377, d238307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74378 q = 1) (hb : d238308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74378, d238308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74378, d238308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74379 q = 1) (hb : d238309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74379, d238309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74379, d238309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74380 q = 1) (hb : d238310 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74380, d238310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74380, d238310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro73685 (p : Pattern) (ha : d53132 p = 1) (hb : d238311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53051 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73657 q ha hb
    | true =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53052 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53057 q = 1) (hb : d238243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53058 q = 1) (hb : d238244 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53058, d238244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53058, d238244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53084 q = 1) (hb : d238270 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53084, d238270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53084, d238270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53132 q = 1) (hb : d238311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53132, d238311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53132, d238311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73686 (p : Pattern) (ha : d53133 p = 1) (hb : d238312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d238247 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53062 q = 1) (hb : d238248 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53062, d238248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53062, d238248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53086 q = 1) (hb : d238272 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53086, d238272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53086, d238272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53133 q = 1) (hb : d238312 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53133, d238312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53133, d238312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73687 (p : Pattern) (ha : d53138 p = 1) (hb : d238317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53051 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73657 q ha hb
    | true =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53052 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53057 q = 1) (hb : d238243 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53057, d238243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53092 q = 1) (hb : d238278 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53092, d238278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53092, d238278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53093 q = 1) (hb : d238279 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53093, d238279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53093, d238279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53138 q = 1) (hb : d238317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53138, d238317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53138, d238317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73688 (p : Pattern) (ha : d53139 p = 1) (hb : d238318 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d238241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73658 q ha hb
    | true =>
      simp only [d53055, d238241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d238242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d238242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d238247 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d238247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53095 q = 1) (hb : d238281 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53095, d238281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53095, d238281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53096 q = 1) (hb : d238282 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53096, d238282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53096, d238282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53139 q = 1) (hb : d238318 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53139, d238318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53139, d238318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73689 (p : Pattern) (ha : d53143 p = 1) (hb : d238322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53118 q = 1) (hb : d238293 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53118, d238293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73679 q ha hb
    | true =>
      simp only [d53118, d238293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53119 q = 1) (hb : d238294 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53119, d238294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53119, d238294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53051 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73657 q ha hb
    | true =>
      simp only [d53051, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53052 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53052, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53120 q = 1) (hb : d238295 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53120, d238295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53120, d238295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53121 q = 1) (hb : d238296 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53121, d238296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53121, d238296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53122 q = 1) (hb : d238297 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53122, d238297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53122, d238297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53143 q = 1) (hb : d238322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53143, d238322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53143, d238322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73690 (p : Pattern) (ha : d74381 p = 1) (hb : d238325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74369 q = 1) (hb : d238237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74369, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73682 q ha hb
    | true =>
      simp only [d74369, d238237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74370 q = 1) (hb : d238238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74370, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74370, d238238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74371 q = 1) (hb : d238301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74371, d238301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74371, d238301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74372 q = 1) (hb : d238302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74372, d238302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74372, d238302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74373 q = 1) (hb : d238303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74373, d238303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74373, d238303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74381 q = 1) (hb : d238325 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74381, d238325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74381, d238325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73691 (p : Pattern) (ha : d74387 p = 1) (hb : d238331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53088 q = 1) (hb : d238274 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53088, d238274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73673 q ha hb
    | true =>
      simp only [d53088, d238274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73674 q ha hb
  have h2 (q : Pattern) (ha : d53089 q = 1) (hb : d238275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53089, d238275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53089, d238275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53090 q = 1) (hb : d238276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53090, d238276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53090, d238276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53091 q = 1) (hb : d238277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53091, d238277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53091, d238277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53098 q = 1) (hb : d238284 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53098, d238284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73675 q ha hb
    | true =>
      simp only [d53098, d238284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73676 q ha hb
  have h6 (q : Pattern) (ha : d53099 q = 1) (hb : d238285 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53099, d238285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53099, d238285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53100 q = 1) (hb : d238286 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53100, d238286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53100, d238286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53124 q = 1) (hb : d238299 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53124, d238299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73680 q ha hb
    | true =>
      simp only [d53124, d238299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73659 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53125 q = 1) (hb : d238300 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d238300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53125, d238300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d74375 q = 1) (hb : d238305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74375, d238305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73683 q ha hb
    | true =>
      simp only [d74375, d238305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74376 q = 1) (hb : d238306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74376, d238306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74376, d238306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d74377 q = 1) (hb : d238307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74377, d238307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74377, d238307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74378 q = 1) (hb : d238308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74378, d238308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74378, d238308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74379 q = 1) (hb : d238309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74379, d238309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74379, d238309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53134 q = 1) (hb : d238313 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53134, d238313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73685 q ha hb
    | true =>
      simp only [d53134, d238313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73686 q ha hb
  have h17 (q : Pattern) (ha : d53135 q = 1) (hb : d238314 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53135, d238314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53135, d238314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d53136 q = 1) (hb : d238315 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53136, d238315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53136, d238315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d53137 q = 1) (hb : d238316 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53137, d238316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53137, d238316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53140 q = 1) (hb : d238319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53140, d238319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73687 q ha hb
    | true =>
      simp only [d53140, d238319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73688 q ha hb
  have h21 (q : Pattern) (ha : d53141 q = 1) (hb : d238320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53141, d238320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53141, d238320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d53142 q = 1) (hb : d238321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53142, d238321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d53142, d238321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d53144 q = 1) (hb : d238323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53144, d238323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73689 q ha hb
    | true =>
      simp only [d53144, d238323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73662 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d53145 q = 1) (hb : d238324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d238324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d53145, d238324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d74382 q = 1) (hb : d238326 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74382, d238326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73690 q ha hb
    | true =>
      simp only [d74382, d238326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d74383 q = 1) (hb : d238327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74383, d238327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d74383, d238327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d74384 q = 1) (hb : d238328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74384, d238328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74384, d238328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74385 q = 1) (hb : d238329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74385, d238329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74385, d238329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74386 q = 1) (hb : d238330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74386, d238330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74386, d238330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74387 q = 1) (hb : d238331 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74387, d238331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74387, d238331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro73692 (p : Pattern) (ha : d74394 p = 1) (hb : d238351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53144 q = 1) (hb : d238323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53144, d238323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73689 q ha hb
    | true =>
      simp only [d53144, d238323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73662 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53145 q = 1) (hb : d238324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d238324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53145, d238324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d74382 q = 1) (hb : d238326 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74382, d238326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73690 q ha hb
    | true =>
      simp only [d74382, d238326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74383 q = 1) (hb : d238327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74383, d238327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74383, d238327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74384 q = 1) (hb : d238328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74384, d238328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74384, d238328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74392 q = 1) (hb : d238349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74392, d238349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74392, d238349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74393 q = 1) (hb : d238350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74393, d238350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74393, d238350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74394 q = 1) (hb : d238351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74394, d238351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74394, d238351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro73693 (p : Pattern) (ha : d29886 p = 1) (hb : d53193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29872 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29872, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29872, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73677 q ha hb
  have h2 (q : Pattern) (ha : d29660 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29660, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73677 q ha hb
    | true =>
      simp only [d29660, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29873 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29873, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29873, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29661 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29661, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29661, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29874 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29874, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29874, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29875 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29875, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29875, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29876 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29876, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29876, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73652 q ha hb
  have h8 (q : Pattern) (ha : d29665 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29665, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73652 q ha hb
    | true =>
      simp only [d29665, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29877 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29877, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29877, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29666 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29666, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29666, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29878 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29878, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29878, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29879 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29879, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29879, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29880 q = 1) (hb : d53187 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29880, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29880, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29881 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29881, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29881, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
  have h15 (q : Pattern) (ha : d29558 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
    | true =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d29882 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29882, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29882, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29559 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d29883 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29883, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29883, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29884 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29884, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d29884, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d29885 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29885, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29885, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d29886 q = 1) (hb : d53193 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29886, d53193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29886, d53193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73694 (p : Pattern) (ha : d53199 p = 1) (hb : d238364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29876 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29876, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29876, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73652 q ha hb
  have h2 (q : Pattern) (ha : d29665 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29665, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73652 q ha hb
    | true =>
      simp only [d29665, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29877 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29877, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29877, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29666 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29666, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29666, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29878 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29878, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29878, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29879 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29879, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29879, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29881 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29881, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29881, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
  have h8 (q : Pattern) (ha : d29558 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
    | true =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29882 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29882, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29882, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29559 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29883 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29883, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29883, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29884 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29884, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29884, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29885 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29885, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29885, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53194 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53194, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53194, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
  have h15 (q : Pattern) (ha : d53023 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
    | true =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d53195 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53195, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53195, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d53024 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d53196 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53196, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53196, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d53197 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53197, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53197, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d53198 q = 1) (hb : d238363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53198, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d53198, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d53199 q = 1) (hb : d238364 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53199, d238364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53199, d238364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73695 (p : Pattern) (ha : d53220 p = 1) (hb : d238380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53200 q = 1) (hb : d238365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53200, d238365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73693 q hb ha
    | true =>
      simp only [d53200, d238365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73694 q ha hb
  have h2 (q : Pattern) (ha : d53201 q = 1) (hb : d238366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53201, d238366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53201, d238366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53202 q = 1) (hb : d238367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53202, d238367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53202, d238367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53205 q = 1) (hb : d238370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53205, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73694 q ha hb
    | true =>
      simp only [d53205, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73668 q ha hb
  have h5 (q : Pattern) (ha : d53206 q = 1) (hb : d238371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53206, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53206, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53207 q = 1) (hb : d238372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53207, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53207, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53208 q = 1) (hb : d238373 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53208, d238373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53208, d238373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53215 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53215, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73668 q ha hb
    | true =>
      simp only [d53215, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73669 q ha hb
  have h9 (q : Pattern) (ha : d53216 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53216, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53216, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53217 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53217, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53217, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53218 q = 1) (hb : d238378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53218, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53218, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53219 q = 1) (hb : d238379 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53219, d238379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53219, d238379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53220 q = 1) (hb : d238380 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53220, d238380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53220, d238380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73696 (p : Pattern) (ha : d53225 p = 1) (hb : d238385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53205 q = 1) (hb : d238370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53205, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73694 q ha hb
    | true =>
      simp only [d53205, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73668 q ha hb
  have h2 (q : Pattern) (ha : d53206 q = 1) (hb : d238371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53206, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53206, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53207 q = 1) (hb : d238372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53207, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53207, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53215 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53215, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73668 q ha hb
    | true =>
      simp only [d53215, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73669 q ha hb
  have h5 (q : Pattern) (ha : d53216 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53216, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53216, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53217 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53217, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53217, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53218 q = 1) (hb : d238378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53218, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53218, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53223 q = 1) (hb : d238383 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53223, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53223, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53224 q = 1) (hb : d238384 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53224, d238384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53224, d238384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53225 q = 1) (hb : d238385 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53225, d238385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53225, d238385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro73697 (p : Pattern) (ha : d53231 p = 1) (hb : d238391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53221 q = 1) (hb : d238381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53221, d238381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73695 q ha hb
    | true =>
      simp only [d53221, d238381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53222 q = 1) (hb : d238382 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53222, d238382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53222, d238382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53226 q = 1) (hb : d238386 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53226, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73696 q ha hb
    | true =>
      simp only [d53226, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53227 q = 1) (hb : d238387 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53227, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53227, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53228 q = 1) (hb : d238388 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53228, d238388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53228, d238388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53229 q = 1) (hb : d238389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53229, d238389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53229, d238389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53230 q = 1) (hb : d238390 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53230, d238390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53230, d238390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53231 q = 1) (hb : d238391 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53231, d238391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53231, d238391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73698 (p : Pattern) (ha : d53239 p = 1) (hb : d238399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53226 q = 1) (hb : d238386 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53226, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73696 q ha hb
    | true =>
      simp only [d53226, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53227 q = 1) (hb : d238387 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53227, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53227, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53234 q = 1) (hb : d238394 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53234, d238394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73670 q ha hb
    | true =>
      simp only [d53234, d238394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53235 q = 1) (hb : d238395 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53235, d238395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53235, d238395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53236 q = 1) (hb : d238396 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53236, d238396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53236, d238396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53237 q = 1) (hb : d238397 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53237, d238397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53237, d238397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53238 q = 1) (hb : d238398 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53238, d238398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53238, d238398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53239 q = 1) (hb : d238399 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53239, d238399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53239, d238399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73699 (p : Pattern) (ha : d74405 p = 1) (hb : d238369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29881 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29881, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29881, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
  have h2 (q : Pattern) (ha : d29558 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73651 q ha hb
    | true =>
      simp only [d29558, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29882 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29882, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29882, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29559 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29559, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29883 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29883, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29883, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29884 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29884, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29884, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53194 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53194, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53194, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
  have h8 (q : Pattern) (ha : d53023 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73653 q ha hb
    | true =>
      simp only [d53023, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53195 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53195, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53195, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53024 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53024, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53196 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53196, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53196, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53197 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53197, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53197, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d53198 q = 1) (hb : d238363 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53198, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53198, d238363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74400 q = 1) (hb : d238359 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74400, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74400, d238359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70785 q ha hb
  have h15 (q : Pattern) (ha : d74356 q = 1) (hb : d238218 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74356, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70785 q ha hb
    | true =>
      simp only [d74356, d238218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74401 q = 1) (hb : d238360 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74401, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74401, d238360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74357 q = 1) (hb : d238219 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74357, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74357, d238219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d74402 q = 1) (hb : d238361 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74402, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74402, d238361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d74403 q = 1) (hb : d238362 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74403, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74403, d238362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d74404 q = 1) (hb : d238368 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74404, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74404, d238368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74405 q = 1) (hb : d238369 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74405, d238369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74405, d238369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73700 (p : Pattern) (ha : d74412 p = 1) (hb : d238385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53205 q = 1) (hb : d238370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53205, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73694 q ha hb
    | true =>
      simp only [d53205, d238370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73668 q ha hb
  have h2 (q : Pattern) (ha : d53206 q = 1) (hb : d238371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53206, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53206, d238371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53207 q = 1) (hb : d238372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53207, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53207, d238372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53215 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53215, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73668 q ha hb
    | true =>
      simp only [d53215, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73669 q ha hb
  have h5 (q : Pattern) (ha : d53216 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53216, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53216, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53217 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53217, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53217, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53218 q = 1) (hb : d238378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53218, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53218, d238378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74407 q = 1) (hb : d238375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d74407, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73699 q ha hb
    | true =>
      simp only [d74407, d238375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70811 q ha hb
  have h9 (q : Pattern) (ha : d74408 q = 1) (hb : d238376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d74408, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74408, d238376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74409 q = 1) (hb : d238377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74409, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74409, d238377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74410 q = 1) (hb : d238383 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d74410, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74410, d238383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74411 q = 1) (hb : d238384 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d74411, d238384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74411, d238384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74412 q = 1) (hb : d238385 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d74412, d238385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74412, d238385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73701 (p : Pattern) (ha : d74418 p = 1) (hb : d238405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74413 q = 1) (hb : d238386 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74413, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73700 q ha hb
    | true =>
      simp only [d74413, d238386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74414 q = 1) (hb : d238387 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74414, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74414, d238387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74415 q = 1) (hb : d238402 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74415, d238402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74415, d238402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74416 q = 1) (hb : d238403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74416, d238403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74416, d238403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74417 q = 1) (hb : d238404 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74417, d238404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74417, d238404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74418 q = 1) (hb : d238405 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74418, d238405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74418, d238405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73702 (p : Pattern) (ha : d74424 p = 1) (hb : d238411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53240 q = 1) (hb : d238400 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53240, d238400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73697 q ha hb
    | true =>
      simp only [d53240, d238400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73698 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53245 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53246 q = 1) (hb : d238401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d238401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53246, d238401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d74419 q = 1) (hb : d238406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74419, d238406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73701 q ha hb
    | true =>
      simp only [d74419, d238406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74420 q = 1) (hb : d238407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74420, d238407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74420, d238407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74421 q = 1) (hb : d238408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74421, d238408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74421, d238408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74422 q = 1) (hb : d238409 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74422, d238409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74422, d238409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74423 q = 1) (hb : d238410 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74423, d238410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74423, d238410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74424 q = 1) (hb : d238411 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74424, d238411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74424, d238411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro73703 (p : Pattern) (ha : d74430 p = 1) (hb : d238428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53071 q = 1) (hb : d238257 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53071, d238257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53071, d238257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73661 q ha hb
  have h2 (q : Pattern) (ha : d53072 q = 1) (hb : d238258 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53072, d238258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53072, d238258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53081 q = 1) (hb : d238267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53081, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73661 q ha hb
    | true =>
      simp only [d53081, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73664 q ha hb
  have h4 (q : Pattern) (ha : d53082 q = 1) (hb : d238268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53082, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53082, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53083 q = 1) (hb : d238269 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53083, d238269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53083, d238269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74388 q = 1) (hb : d238332 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74388, d238332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73684 q ha hb
    | true =>
      simp only [d74388, d238332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73691 q ha hb
  have h7 (q : Pattern) (ha : d53165 q = 1) (hb : d238345 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53165, d238345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73665 q ha hb
    | true =>
      simp only [d53165, d238345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73666 q ha hb
  have h8 (q : Pattern) (ha : d74389 q = 1) (hb : d238346 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74389, d238346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74389, d238346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74390 q = 1) (hb : d238347 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74390, d238347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74390, d238347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74391 q = 1) (hb : d238348 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74391, d238348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74391, d238348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74395 q = 1) (hb : d238352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74395, d238352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74395, d238352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73692 q ha hb
  have h12 (q : Pattern) (ha : d53174 q = 1) (hb : d238354 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53174, d238354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53174, d238354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73667 q ha hb
  have h13 (q : Pattern) (ha : d74396 q = 1) (hb : d238355 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74396, d238355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74396, d238355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74397 q = 1) (hb : d238356 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74397, d238356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74397, d238356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74398 q = 1) (hb : d238357 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74398, d238357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74398, d238357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74399 q = 1) (hb : d238358 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74399, d238358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74399, d238358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74425 q = 1) (hb : d238412 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74425, d238412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74425, d238412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73702 q ha hb
  have h18 (q : Pattern) (ha : d53260 q = 1) (hb : d238423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53260, d238423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53260, d238423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73672 q ha hb
  have h19 (q : Pattern) (ha : d74426 q = 1) (hb : d238424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74426, d238424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74426, d238424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74427 q = 1) (hb : d238425 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74427, d238425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74427, d238425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74428 q = 1) (hb : d238426 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74428, d238426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74428, d238426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74429 q = 1) (hb : d238427 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74429, d238427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74429, d238427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74430 q = 1) (hb : d238428 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74430, d238428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74430, d238428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro73704 (p : Pattern) (ha : d74436 p = 1) (hb : d238434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74431 q = 1) (hb : d238429 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74431, d238429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74431, d238429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73703 q ha hb
  have h2 (q : Pattern) (ha : d74432 q = 1) (hb : d238430 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74432, d238430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74432, d238430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74433 q = 1) (hb : d238431 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74433, d238431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74433, d238431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74434 q = 1) (hb : d238432 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74434, d238432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74434, d238432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74435 q = 1) (hb : d238433 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74435, d238433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74435, d238433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74436 q = 1) (hb : d238434 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74436, d238434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74436, d238434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73705 (p : Pattern) (ha : d30087 p = 1) (hb : d53313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53282 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30077 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30078 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30078, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30079 q = 1) (hb : d53289 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30079, d53289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30079, d53289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30080 q = 1) (hb : d53290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30080, d53290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30080, d53290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30081 q = 1) (hb : d53291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30081, d53291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30081, d53291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53298 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d30082 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d30083 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30083, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30084 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30084, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53310 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d30085 q = 1) (hb : d53311 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30085, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30086 q = 1) (hb : d53312 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30086, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30087 q = 1) (hb : d53313 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30087, d53313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30087, d53313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro73706 (p : Pattern) (ha : d30097 p = 1) (hb : d53331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53282 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30078 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53298 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30082 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30083 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30083, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30084 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30084, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30084, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53310 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30085 q = 1) (hb : d53311 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30085, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30085, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d30086 q = 1) (hb : d53312 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30086, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30086, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d30092 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d30092, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d30093 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30093, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30094 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30094, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d30095 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d30095, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d30096 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d30096, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h21 (q : Pattern) (ha : d30097 q = 1) (hb : d53331 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30097, d53331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30097, d53331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73707 (p : Pattern) (ha : d53343 p = 1) (hb : d238441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53298 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30083 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53319 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30092 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30092, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d30092, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30093 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30093, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30093, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30094 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30094, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30094, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30095 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30095, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30095, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d30096 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30096, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30096, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53338 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h15 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h16 (q : Pattern) (ha : d30103 q = 1) (hb : d53339 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30103, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30103, d53339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d53341 q = 1) (hb : d238439 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d53341, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d53341, d238439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d53342 q = 1) (hb : d238440 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d53342, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53342, d238440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h20 (q : Pattern) (ha : d53343 q = 1) (hb : d238441 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d53343, d238441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d53343, d238441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro73708 (p : Pattern) (ha : d53349 p = 1) (hb : d238447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30088 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73705 q ha hb
    | true =>
      simp only [d30088, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30089 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30089, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30090 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30090, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30090, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30091 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30091, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30091, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30098 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
    | true =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30099 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30100 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30101 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30101, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30102 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30102, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30102, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53344 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
    | true =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53345 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d53346 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53346, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53346, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53347 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53347, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53347, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d53348 q = 1) (hb : d238446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53348, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53348, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53349 q = 1) (hb : d238447 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53349, d238447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d53349, d238447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73709 (p : Pattern) (ha : d53351 p = 1) (hb : d238449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30098 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
    | true =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30099 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30100 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30101 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30101, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53344 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
    | true =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53345 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53346 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53346, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53346, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53347 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53347, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53347, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53348 q = 1) (hb : d238446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53348, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53348, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53350 q = 1) (hb : d238448 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53350, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53350, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53351 q = 1) (hb : d238449 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53351, d238449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53351, d238449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73710 (p : Pattern) (ha : d53364 p = 1) (hb : d238453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53344 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
    | true =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53345 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53346 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53346, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53346, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53347 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53347, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53347, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53350 q = 1) (hb : d238448 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53350, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53350, d238448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53363 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53364 q = 1) (hb : d238453 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53364, d238453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53364, d238453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro73711 (p : Pattern) (ha : d53371 p = 1) (hb : d238460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53352 q = 1) (hb : d238450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53352, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73708 q ha hb
    | true =>
      simp only [d53352, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73709 q ha hb
  have h2 (q : Pattern) (ha : d53353 q = 1) (hb : d238451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53353, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53353, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53354 q = 1) (hb : d238452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53354, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53354, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53365 q = 1) (hb : d238454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53365, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73709 q ha hb
    | true =>
      simp only [d53365, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73710 q ha hb
  have h5 (q : Pattern) (ha : d53366 q = 1) (hb : d238455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53366, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53366, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53367 q = 1) (hb : d238456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53367, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53367, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53368 q = 1) (hb : d238457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53368, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53368, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53369 q = 1) (hb : d238458 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53369, d238458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53369, d238458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53370 q = 1) (hb : d238459 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53370, d238459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53370, d238459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53371 q = 1) (hb : d238460 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53371, d238460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53371, d238460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro73712 (p : Pattern) (ha : d53375 p = 1) (hb : d238464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53365 q = 1) (hb : d238454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53365, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73709 q ha hb
    | true =>
      simp only [d53365, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73710 q ha hb
  have h2 (q : Pattern) (ha : d53366 q = 1) (hb : d238455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53366, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53366, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53367 q = 1) (hb : d238456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53367, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53367, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53369 q = 1) (hb : d238458 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53369, d238458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53369, d238458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53374 q = 1) (hb : d238463 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53374, d238463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53374, d238463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53375 q = 1) (hb : d238464 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53375, d238464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53375, d238464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73713 (p : Pattern) (ha : d53381 p = 1) (hb : d238470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53372 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73711 q ha hb
    | true =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53373 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53378 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53379 q = 1) (hb : d238468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53379, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53379, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53380 q = 1) (hb : d238469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53380, d238469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53380, d238469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53381 q = 1) (hb : d238470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53381, d238470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53381, d238470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73714 (p : Pattern) (ha : d53385 p = 1) (hb : d238474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53383 q = 1) (hb : d238472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53383, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53383, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53384 q = 1) (hb : d238473 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53384, d238473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53384, d238473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53385 q = 1) (hb : d238474 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53385, d238474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53385, d238474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73715 (p : Pattern) (ha : d53391 p = 1) (hb : d238480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53386 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73713 q ha hb
    | true =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73714 q ha hb
  have h2 (q : Pattern) (ha : d53387 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53387, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53387, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53388 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53388, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53388, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53389 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53389, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53389, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53390 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53390, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53390, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53391 q = 1) (hb : d238480 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53391, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53391, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73716 (p : Pattern) (ha : d53394 p = 1) (hb : d238483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53372 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73711 q ha hb
    | true =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53373 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53378 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53379 q = 1) (hb : d238468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53379, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53379, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53380 q = 1) (hb : d238469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53380, d238469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53380, d238469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53394 q = 1) (hb : d238483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53394, d238483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53394, d238483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73717 (p : Pattern) (ha : d53395 p = 1) (hb : d238484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53383 q = 1) (hb : d238472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53383, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53383, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53384 q = 1) (hb : d238473 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53384, d238473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53384, d238473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53395 q = 1) (hb : d238484 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53395, d238484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53395, d238484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73718 (p : Pattern) (ha : d53401 p = 1) (hb : d238490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53386 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73713 q ha hb
    | true =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73714 q ha hb
  have h2 (q : Pattern) (ha : d53387 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53387, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53387, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53388 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53388, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53388, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53389 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53389, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53389, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53390 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53390, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53390, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53396 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53396, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73716 q ha hb
    | true =>
      simp only [d53396, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73717 q ha hb
  have h7 (q : Pattern) (ha : d53397 q = 1) (hb : d238486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53397, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53397, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53398 q = 1) (hb : d238487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53398, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53398, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53399 q = 1) (hb : d238488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53399, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53399, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53400 q = 1) (hb : d238489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53400, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53400, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53401 q = 1) (hb : d238490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53401, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53401, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73719 (p : Pattern) (ha : d53475 p = 1) (hb : d238578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53386 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73713 q ha hb
    | true =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73714 q ha hb
  have h2 (q : Pattern) (ha : d53387 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53387, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53387, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53388 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53388, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53388, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53389 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53389, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53389, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53390 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53390, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53390, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53470 q = 1) (hb : d238573 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53470, d238573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73714 q ha hb
    | true =>
      simp only [d53470, d238573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53471 q = 1) (hb : d238574 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53471, d238574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53471, d238574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53472 q = 1) (hb : d238575 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53472, d238575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53472, d238575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53473 q = 1) (hb : d238576 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53473, d238576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53473, d238576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53474 q = 1) (hb : d238577 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53474, d238577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53474, d238577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53475 q = 1) (hb : d238578 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53475, d238578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53475, d238578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73720 (p : Pattern) (ha : d53481 p = 1) (hb : d238584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53470 q = 1) (hb : d238573 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53470, d238573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73714 q ha hb
    | true =>
      simp only [d53470, d238573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53471 q = 1) (hb : d238574 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53471, d238574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53471, d238574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53472 q = 1) (hb : d238575 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53472, d238575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53472, d238575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53473 q = 1) (hb : d238576 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53473, d238576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53473, d238576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53474 q = 1) (hb : d238577 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53474, d238577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53474, d238577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53476 q = 1) (hb : d238579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53476, d238579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73717 q ha hb
    | true =>
      simp only [d53476, d238579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53477 q = 1) (hb : d238580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53477, d238580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53477, d238580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53478 q = 1) (hb : d238581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53478, d238581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53478, d238581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53479 q = 1) (hb : d238582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53479, d238582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53479, d238582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53480 q = 1) (hb : d238583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53480, d238583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53480, d238583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53481 q = 1) (hb : d238584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53481, d238584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53481, d238584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73721 (p : Pattern) (ha : d53490 p = 1) (hb : d238593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53476 q = 1) (hb : d238579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53476, d238579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73717 q ha hb
    | true =>
      simp only [d53476, d238579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53477 q = 1) (hb : d238580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53477, d238580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53477, d238580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53478 q = 1) (hb : d238581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53478, d238581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53478, d238581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53479 q = 1) (hb : d238582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53479, d238582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53479, d238582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53480 q = 1) (hb : d238583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53480, d238583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53480, d238583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53490 q = 1) (hb : d238593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53490, d238593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53490, d238593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73722 (p : Pattern) (ha : d53521 p = 1) (hb : d238609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30408 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
  have h2 (q : Pattern) (ha : d30098 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
    | true =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30409 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30409, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30099 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30410 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30410, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30411 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30411, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53511 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53511, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53511, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
  have h8 (q : Pattern) (ha : d53344 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
    | true =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53512 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53512, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53512, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53345 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53513 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53513, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53513, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53514 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53514, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53514, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d53515 q = 1) (hb : d238603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53515, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53515, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53520 q = 1) (hb : d238608 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53520, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53520, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d53521 q = 1) (hb : d238609 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53521, d238609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53521, d238609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73723 (p : Pattern) (ha : d53531 p = 1) (hb : d238614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53511 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53511, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53511, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
  have h2 (q : Pattern) (ha : d53344 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
    | true =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53512 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53512, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53512, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53345 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53513 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53513, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53513, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53514 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53514, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53514, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53520 q = 1) (hb : d238608 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53520, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53520, d238608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53530 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d53531 q = 1) (hb : d238614 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53531, d238614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53531, d238614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro73724 (p : Pattern) (ha : d53550 p = 1) (hb : d238633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53532 q = 1) (hb : d238615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53532, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73722 q ha hb
    | true =>
      simp only [d53532, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73723 q ha hb
  have h2 (q : Pattern) (ha : d53533 q = 1) (hb : d238616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53533, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53533, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53534 q = 1) (hb : d238617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53534, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53534, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53540 q = 1) (hb : d238623 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53540, d238623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53540, d238623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53549 q = 1) (hb : d238632 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53549, d238632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53549, d238632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53550 q = 1) (hb : d238633 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53550, d238633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53550, d238633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73725 (p : Pattern) (ha : d53561 p = 1) (hb : d238671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53551 q = 1) (hb : d238634 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53551, d238634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73724 q ha hb
    | true =>
      simp only [d53551, d238634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53552 q = 1) (hb : d238635 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53552, d238635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53552, d238635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53558 q = 1) (hb : d238668 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53558, d238668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53558, d238668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53559 q = 1) (hb : d238669 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53559, d238669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53559, d238669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53560 q = 1) (hb : d238670 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53560, d238670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53560, d238670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53561 q = 1) (hb : d238671 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53561, d238671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53561, d238671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73726 (p : Pattern) (ha : d53576 p = 1) (hb : d238677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53571 q = 1) (hb : d238672 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53571, d238672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73725 q ha hb
    | true =>
      simp only [d53571, d238672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53572 q = 1) (hb : d238673 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53572, d238673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53572, d238673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53573 q = 1) (hb : d238674 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53573, d238674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53573, d238674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53574 q = 1) (hb : d238675 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53574, d238675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53574, d238675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53575 q = 1) (hb : d238676 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53575, d238676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53575, d238676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53576 q = 1) (hb : d238677 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53576, d238677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53576, d238677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73727 (p : Pattern) (ha : d53406 p = 1) (hb : d238495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53372 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73711 q ha hb
    | true =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53373 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53378 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53379 q = 1) (hb : d238468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53379, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53379, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53405 q = 1) (hb : d238494 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53405, d238494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53405, d238494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53406 q = 1) (hb : d238495 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53406, d238495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53406, d238495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73728 (p : Pattern) (ha : d53408 p = 1) (hb : d238497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53383 q = 1) (hb : d238472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53383, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53383, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53407 q = 1) (hb : d238496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53407, d238496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53407, d238496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53408 q = 1) (hb : d238497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53408, d238497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53408, d238497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73729 (p : Pattern) (ha : d53415 p = 1) (hb : d238504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53372 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73711 q ha hb
    | true =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53373 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53378 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53413 q = 1) (hb : d238502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53413, d238502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53413, d238502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53414 q = 1) (hb : d238503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53414, d238503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53414, d238503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53415 q = 1) (hb : d238504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53415, d238504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53415, d238504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73730 (p : Pattern) (ha : d53418 p = 1) (hb : d238507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53416 q = 1) (hb : d238505 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53416, d238505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53416, d238505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53417 q = 1) (hb : d238506 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53417, d238506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53417, d238506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53418 q = 1) (hb : d238507 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53418, d238507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53418, d238507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73731 (p : Pattern) (ha : d30204 p = 1) (hb : d53428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30199 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30199, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70838 q ha hb
    | true =>
      simp only [d30199, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30200 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30200, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30200, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30201 q = 1) (hb : d53425 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30201, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30201, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30202 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30202, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30202, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30088 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73705 q ha hb
    | true =>
      simp only [d30088, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30089 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30089, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30090 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30090, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30090, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30091 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30091, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30091, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30203 q = 1) (hb : d53427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30203, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30203, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30098 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
    | true =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30099 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30100 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30101 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30101, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30102 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30102, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30102, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30204 q = 1) (hb : d53428 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30204, d53428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30204, d53428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73732 (p : Pattern) (ha : d53434 p = 1) (hb : d238516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53429 q = 1) (hb : d238511 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53429, d238511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73731 q hb ha
    | true =>
      simp only [d53429, d238511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73708 q ha hb
  have h2 (q : Pattern) (ha : d53430 q = 1) (hb : d238512 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53430, d238512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53430, d238512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53431 q = 1) (hb : d238513 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53431, d238513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53431, d238513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53352 q = 1) (hb : d238450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53352, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73708 q ha hb
    | true =>
      simp only [d53352, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73709 q ha hb
  have h5 (q : Pattern) (ha : d53353 q = 1) (hb : d238451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53353, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53353, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53354 q = 1) (hb : d238452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53354, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53354, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53432 q = 1) (hb : d238514 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53432, d238514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53432, d238514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53365 q = 1) (hb : d238454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53365, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73709 q ha hb
    | true =>
      simp only [d53365, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73710 q ha hb
  have h9 (q : Pattern) (ha : d53366 q = 1) (hb : d238455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53366, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53366, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53367 q = 1) (hb : d238456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53367, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53367, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53368 q = 1) (hb : d238457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53368, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53368, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53433 q = 1) (hb : d238515 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53433, d238515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53433, d238515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53434 q = 1) (hb : d238516 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53434, d238516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53434, d238516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73733 (p : Pattern) (ha : d53440 p = 1) (hb : d238522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53435 q = 1) (hb : d238517 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53435, d238517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73732 q ha hb
    | true =>
      simp only [d53435, d238517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53436 q = 1) (hb : d238518 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53436, d238518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53436, d238518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53372 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73711 q ha hb
    | true =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53373 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53437 q = 1) (hb : d238519 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53437, d238519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53437, d238519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53438 q = 1) (hb : d238520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53438, d238520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53438, d238520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53439 q = 1) (hb : d238521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53439, d238521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53439, d238521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53440 q = 1) (hb : d238522 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53440, d238522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53440, d238522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73734 (p : Pattern) (ha : d74452 p = 1) (hb : d238531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30098 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
    | true =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30099 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30100 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30100, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30100, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30101 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30101, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30101, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53344 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
    | true =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53345 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53346 q = 1) (hb : d238444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53346, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53346, d238444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53347 q = 1) (hb : d238445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53347, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53347, d238445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53348 q = 1) (hb : d238446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53348, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d53348, d238446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74447 q = 1) (hb : d238526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70842 q ha hb
    | true =>
      simp only [d74447, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d74448 q = 1) (hb : d238527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74448, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74449 q = 1) (hb : d238528 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74449, d238528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74449, d238528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74450 q = 1) (hb : d238529 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74450, d238529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74450, d238529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d74451 q = 1) (hb : d238530 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74451, d238530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74451, d238530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74452 q = 1) (hb : d238531 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74452, d238531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74452, d238531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73735 (p : Pattern) (ha : d74459 p = 1) (hb : d238538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53352 q = 1) (hb : d238450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53352, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73708 q ha hb
    | true =>
      simp only [d53352, d238450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73709 q ha hb
  have h2 (q : Pattern) (ha : d53353 q = 1) (hb : d238451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53353, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53353, d238451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53354 q = 1) (hb : d238452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53354, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53354, d238452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53365 q = 1) (hb : d238454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53365, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73709 q ha hb
    | true =>
      simp only [d53365, d238454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73710 q ha hb
  have h5 (q : Pattern) (ha : d53366 q = 1) (hb : d238455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53366, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53366, d238455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53367 q = 1) (hb : d238456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53367, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53367, d238456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53368 q = 1) (hb : d238457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53368, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53368, d238457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74454 q = 1) (hb : d238533 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d74454, d238533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73734 q ha hb
    | true =>
      simp only [d74454, d238533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70843 q ha hb
  have h9 (q : Pattern) (ha : d74455 q = 1) (hb : d238534 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d74455, d238534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74455, d238534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74456 q = 1) (hb : d238535 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74456, d238535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74456, d238535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74457 q = 1) (hb : d238536 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d74457, d238536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74457, d238536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74458 q = 1) (hb : d238537 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d74458, d238537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74458, d238537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74459 q = 1) (hb : d238538 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d74459, d238538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74459, d238538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73736 (p : Pattern) (ha : d74465 p = 1) (hb : d238544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74460 q = 1) (hb : d238539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74460, d238539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73735 q ha hb
    | true =>
      simp only [d74460, d238539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74461 q = 1) (hb : d238540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74461, d238540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74461, d238540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74462 q = 1) (hb : d238541 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74462, d238541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74462, d238541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74463 q = 1) (hb : d238542 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74463, d238542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74463, d238542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74464 q = 1) (hb : d238543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74464, d238543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74464, d238543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74465 q = 1) (hb : d238544 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74465, d238544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74465, d238544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73737 (p : Pattern) (ha : d74471 p = 1) (hb : d238550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53409 q = 1) (hb : d238498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53409, d238498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73727 q ha hb
    | true =>
      simp only [d53409, d238498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73728 q ha hb
  have h2 (q : Pattern) (ha : d53410 q = 1) (hb : d238499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53410, d238499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53410, d238499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53411 q = 1) (hb : d238500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53411, d238500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53411, d238500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53412 q = 1) (hb : d238501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53412, d238501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53412, d238501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53419 q = 1) (hb : d238508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53419, d238508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73729 q ha hb
    | true =>
      simp only [d53419, d238508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73730 q ha hb
  have h6 (q : Pattern) (ha : d53420 q = 1) (hb : d238509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53420, d238509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53420, d238509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53421 q = 1) (hb : d238510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53421, d238510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53421, d238510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53441 q = 1) (hb : d238523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53441, d238523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73733 q ha hb
    | true =>
      simp only [d53441, d238523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73713 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53442 q = 1) (hb : d238524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d238524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53442, d238524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d74466 q = 1) (hb : d238545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74466, d238545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73736 q ha hb
    | true =>
      simp only [d74466, d238545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74467 q = 1) (hb : d238546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74467, d238546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74467, d238546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d74468 q = 1) (hb : d238547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74468, d238547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74468, d238547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74469 q = 1) (hb : d238548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74469, d238548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74469, d238548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74470 q = 1) (hb : d238549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74470, d238549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74470, d238549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74471 q = 1) (hb : d238550 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74471, d238550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74471, d238550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro73738 (p : Pattern) (ha : d53449 p = 1) (hb : d238551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53372 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73711 q ha hb
    | true =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53373 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53378 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53379 q = 1) (hb : d238468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53379, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53379, d238468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53405 q = 1) (hb : d238494 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53405, d238494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53405, d238494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53449 q = 1) (hb : d238551 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53449, d238551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53449, d238551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73739 (p : Pattern) (ha : d53450 p = 1) (hb : d238552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53383 q = 1) (hb : d238472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53383, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53383, d238472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53407 q = 1) (hb : d238496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53407, d238496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53407, d238496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53450 q = 1) (hb : d238552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53450, d238552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53450, d238552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73740 (p : Pattern) (ha : d53455 p = 1) (hb : d238557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53372 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73711 q ha hb
    | true =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53373 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53378 q = 1) (hb : d238467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53378, d238467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53413 q = 1) (hb : d238502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53413, d238502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53413, d238502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53414 q = 1) (hb : d238503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53414, d238503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53414, d238503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53455 q = 1) (hb : d238557 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53455, d238557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53455, d238557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73741 (p : Pattern) (ha : d53456 p = 1) (hb : d238558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d238465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73712 q ha hb
    | true =>
      simp only [d53376, d238465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d238466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d238466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d238471 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d238471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53416 q = 1) (hb : d238505 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53416, d238505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53416, d238505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53417 q = 1) (hb : d238506 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53417, d238506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53417, d238506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53456 q = 1) (hb : d238558 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53456, d238558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53456, d238558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73742 (p : Pattern) (ha : d53460 p = 1) (hb : d238562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53435 q = 1) (hb : d238517 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53435, d238517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73732 q ha hb
    | true =>
      simp only [d53435, d238517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53436 q = 1) (hb : d238518 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53436, d238518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53436, d238518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53372 q = 1) (hb : d238461 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73711 q ha hb
    | true =>
      simp only [d53372, d238461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53373 q = 1) (hb : d238462 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53373, d238462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53437 q = 1) (hb : d238519 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53437, d238519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53437, d238519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53438 q = 1) (hb : d238520 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53438, d238520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53438, d238520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53439 q = 1) (hb : d238521 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53439, d238521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53439, d238521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53460 q = 1) (hb : d238562 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53460, d238562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53460, d238562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73743 (p : Pattern) (ha : d74472 p = 1) (hb : d238565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74460 q = 1) (hb : d238539 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74460, d238539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73735 q ha hb
    | true =>
      simp only [d74460, d238539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74461 q = 1) (hb : d238540 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74461, d238540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74461, d238540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74462 q = 1) (hb : d238541 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74462, d238541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74462, d238541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74463 q = 1) (hb : d238542 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74463, d238542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74463, d238542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74464 q = 1) (hb : d238543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74464, d238543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74464, d238543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74472 q = 1) (hb : d238565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74472, d238565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74472, d238565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73744 (p : Pattern) (ha : d74478 p = 1) (hb : d238571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53409 q = 1) (hb : d238498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53409, d238498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73727 q ha hb
    | true =>
      simp only [d53409, d238498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73728 q ha hb
  have h2 (q : Pattern) (ha : d53410 q = 1) (hb : d238499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53410, d238499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53410, d238499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53411 q = 1) (hb : d238500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53411, d238500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53411, d238500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53412 q = 1) (hb : d238501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53412, d238501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53412, d238501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53419 q = 1) (hb : d238508 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53419, d238508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73729 q ha hb
    | true =>
      simp only [d53419, d238508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73730 q ha hb
  have h6 (q : Pattern) (ha : d53420 q = 1) (hb : d238509 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53420, d238509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53420, d238509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53421 q = 1) (hb : d238510 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53421, d238510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53421, d238510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53441 q = 1) (hb : d238523 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53441, d238523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73733 q ha hb
    | true =>
      simp only [d53441, d238523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73713 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53442 q = 1) (hb : d238524 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d238524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53442, d238524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d74466 q = 1) (hb : d238545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74466, d238545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73736 q ha hb
    | true =>
      simp only [d74466, d238545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74467 q = 1) (hb : d238546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74467, d238546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74467, d238546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d74468 q = 1) (hb : d238547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74468, d238547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74468, d238547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74469 q = 1) (hb : d238548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74469, d238548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74469, d238548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74470 q = 1) (hb : d238549 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74470, d238549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74470, d238549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53451 q = 1) (hb : d238553 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53451, d238553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73738 q ha hb
    | true =>
      simp only [d53451, d238553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73739 q ha hb
  have h17 (q : Pattern) (ha : d53452 q = 1) (hb : d238554 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53452, d238554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53452, d238554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d53453 q = 1) (hb : d238555 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53453, d238555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d53453, d238555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d53454 q = 1) (hb : d238556 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53454, d238556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53454, d238556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d53457 q = 1) (hb : d238559 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53457, d238559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73740 q ha hb
    | true =>
      simp only [d53457, d238559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73741 q ha hb
  have h21 (q : Pattern) (ha : d53458 q = 1) (hb : d238560 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53458, d238560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53458, d238560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d53459 q = 1) (hb : d238561 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53459, d238561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d53459, d238561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d53461 q = 1) (hb : d238563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53461, d238563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73742 q ha hb
    | true =>
      simp only [d53461, d238563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73716 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d53462 q = 1) (hb : d238564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d238564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d53462, d238564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d74473 q = 1) (hb : d238566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74473, d238566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73743 q ha hb
    | true =>
      simp only [d74473, d238566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d74474 q = 1) (hb : d238567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74474, d238567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d74474, d238567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d74475 q = 1) (hb : d238568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74475, d238568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d74475, d238568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74476 q = 1) (hb : d238569 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74476, d238569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d74476, d238569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74477 q = 1) (hb : d238570 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74477, d238570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74477, d238570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74478 q = 1) (hb : d238571 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74478, d238571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74478, d238571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro73745 (p : Pattern) (ha : d74485 p = 1) (hb : d238591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53461 q = 1) (hb : d238563 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53461, d238563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73742 q ha hb
    | true =>
      simp only [d53461, d238563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73716 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53462 q = 1) (hb : d238564 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d238564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53462, d238564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d74473 q = 1) (hb : d238566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74473, d238566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73743 q ha hb
    | true =>
      simp only [d74473, d238566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74474 q = 1) (hb : d238567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74474, d238567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74474, d238567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74475 q = 1) (hb : d238568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74475, d238568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74475, d238568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74483 q = 1) (hb : d238589 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74483, d238589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74483, d238589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74484 q = 1) (hb : d238590 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74484, d238590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74484, d238590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74485 q = 1) (hb : d238591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74485, d238591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74485, d238591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro73746 (p : Pattern) (ha : d30413 p = 1) (hb : d53510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30399 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30399, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30399, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70838 q ha hb
  have h2 (q : Pattern) (ha : d30199 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30199, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70838 q ha hb
    | true =>
      simp only [d30199, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30400 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30400, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30400, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30200 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30200, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30200, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30401 q = 1) (hb : d53498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30401, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30401, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30402 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30402, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30402, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30403 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30403, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30403, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73705 q ha hb
  have h8 (q : Pattern) (ha : d30088 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73705 q ha hb
    | true =>
      simp only [d30088, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30404 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30404, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30404, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30089 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30089, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30405 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30405, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30405, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30406 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30406, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30406, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30407 q = 1) (hb : d53504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30407, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30407, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30408 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
  have h15 (q : Pattern) (ha : d30098 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
    | true =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30409 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30409, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30099 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30410 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30410, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30411 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d30411, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d30412 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30412, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30412, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d30413 q = 1) (hb : d53510 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30413, d53510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30413, d53510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73747 (p : Pattern) (ha : d53516 p = 1) (hb : d238604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30403 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30403, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30403, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73705 q ha hb
  have h2 (q : Pattern) (ha : d30088 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30088, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73705 q ha hb
    | true =>
      simp only [d30088, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30404 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30404, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30404, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30089 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30089, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30089, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30405 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30405, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30405, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30406 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30406, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30406, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30408 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
  have h8 (q : Pattern) (ha : d30098 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
    | true =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30409 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30409, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30099 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30410 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30410, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30411 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30411, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30412 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30412, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30412, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53511 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53511, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53511, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
  have h15 (q : Pattern) (ha : d53344 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
    | true =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d53512 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53512, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53512, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d53345 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d53513 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53513, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53513, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d53514 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53514, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d53514, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d53515 q = 1) (hb : d238603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53515, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d53515, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d53516 q = 1) (hb : d238604 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53516, d238604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d53516, d238604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73748 (p : Pattern) (ha : d53537 p = 1) (hb : d238620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53517 q = 1) (hb : d238605 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53517, d238605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73746 q hb ha
    | true =>
      simp only [d53517, d238605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73747 q ha hb
  have h2 (q : Pattern) (ha : d53518 q = 1) (hb : d238606 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53518, d238606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53518, d238606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53519 q = 1) (hb : d238607 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53519, d238607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53519, d238607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53522 q = 1) (hb : d238610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53522, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73747 q ha hb
    | true =>
      simp only [d53522, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73722 q ha hb
  have h5 (q : Pattern) (ha : d53523 q = 1) (hb : d238611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53523, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53523, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53524 q = 1) (hb : d238612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53524, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53524, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53525 q = 1) (hb : d238613 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53525, d238613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53525, d238613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53532 q = 1) (hb : d238615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53532, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73722 q ha hb
    | true =>
      simp only [d53532, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73723 q ha hb
  have h9 (q : Pattern) (ha : d53533 q = 1) (hb : d238616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53533, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53533, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53534 q = 1) (hb : d238617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53534, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53534, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53535 q = 1) (hb : d238618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53535, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53535, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53536 q = 1) (hb : d238619 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53536, d238619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53536, d238619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53537 q = 1) (hb : d238620 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53537, d238620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53537, d238620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73749 (p : Pattern) (ha : d53542 p = 1) (hb : d238625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53522 q = 1) (hb : d238610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53522, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73747 q ha hb
    | true =>
      simp only [d53522, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73722 q ha hb
  have h2 (q : Pattern) (ha : d53523 q = 1) (hb : d238611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53523, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53523, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53524 q = 1) (hb : d238612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53524, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53524, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53532 q = 1) (hb : d238615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53532, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73722 q ha hb
    | true =>
      simp only [d53532, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73723 q ha hb
  have h5 (q : Pattern) (ha : d53533 q = 1) (hb : d238616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53533, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53533, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53534 q = 1) (hb : d238617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53534, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53534, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53535 q = 1) (hb : d238618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53535, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53535, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53540 q = 1) (hb : d238623 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53540, d238623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53540, d238623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53541 q = 1) (hb : d238624 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53541, d238624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53541, d238624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53542 q = 1) (hb : d238625 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53542, d238625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53542, d238625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
end NetHack.Soko22Hazard87
