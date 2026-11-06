import NetHack.Soko22Hazard87.AndIntroBlocks0174
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro43750 (p : Pattern) (ha : d101901 p = 1) (hb : d129493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101896 q = 1) (hb : d129488 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101896, d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101896, d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43749 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9437 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101897 q = 1) (hb : d129489 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101897, d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101897, d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101898 q = 1) (hb : d129490 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101898, d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101898, d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101899 q = 1) (hb : d129491 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101899, d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101899, d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101900 q = 1) (hb : d129492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101900, d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101900, d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101901 q = 1) (hb : d129493 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101901, d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101901, d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43751 (p : Pattern) (ha : d101907 p = 1) (hb : d129499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d9324 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101886 q = 1) (hb : d129478 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101886, d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101886, d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43748 q ha hb
  have h3 (q : Pattern) (ha : d101887 q = 1) (hb : d129479 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101887, d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101887, d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101888 q = 1) (hb : d129480 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101888, d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101888, d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101889 q = 1) (hb : d129481 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101889, d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101889, d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101890 q = 1) (hb : d129482 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101890, d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d101890, d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101902 q = 1) (hb : d129494 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101902, d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101902, d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43750 q ha hb
  have h8 (q : Pattern) (ha : d101903 q = 1) (hb : d129495 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101903, d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101903, d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101904 q = 1) (hb : d129496 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101904, d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101904, d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101905 q = 1) (hb : d129497 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101905, d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101905, d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d101906 q = 1) (hb : d129498 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101906, d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101906, d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d101907 q = 1) (hb : d129499 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101907, d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101907, d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43752 (p : Pattern) (ha : d101912 p = 1) (hb : d129505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101908 q = 1) (hb : d129501 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101908, d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101908, d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9547 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101909 q = 1) (hb : d129502 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101909, d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101909, d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101910 q = 1) (hb : d129503 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101910, d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101910, d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101911 q = 1) (hb : d129504 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101911, d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101911, d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101912 q = 1) (hb : d129505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101912, d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101912, d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43753 (p : Pattern) (ha : d101918 p = 1) (hb : d129511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101913 q = 1) (hb : d129506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101913, d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101913, d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43752 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101914 q = 1) (hb : d129507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101914, d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101914, d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101915 q = 1) (hb : d129508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101915, d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101915, d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101916 q = 1) (hb : d129509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101916, d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101916, d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101917 q = 1) (hb : d129510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101917, d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101917, d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101918 q = 1) (hb : d129511 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101918, d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101918, d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43754 (p : Pattern) (ha : d101924 p = 1) (hb : d129517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101919 q = 1) (hb : d129512 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101919, d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101919, d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43753 q ha hb
  have h2 (q : Pattern) (ha : d101920 q = 1) (hb : d129513 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101920, d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101920, d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101921 q = 1) (hb : d129514 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101921, d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101921, d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101922 q = 1) (hb : d129515 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101922, d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101922, d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101923 q = 1) (hb : d129516 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101923, d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101923, d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101924 q = 1) (hb : d129517 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101924, d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101924, d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43755 (p : Pattern) (ha : d101930 p = 1) (hb : d129524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129519 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101926 q = 1) (hb : d129520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101926, d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101926, d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d9716 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101927 q = 1) (hb : d129521 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101927, d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101927, d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101928 q = 1) (hb : d129522 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101928, d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101928, d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101929 q = 1) (hb : d129523 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101929, d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101929, d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101930 q = 1) (hb : d129524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101930, d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101930, d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43756 (p : Pattern) (ha : d101936 p = 1) (hb : d129530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101931 q = 1) (hb : d129525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101931, d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101931, d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43755 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9732 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101932 q = 1) (hb : d129526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101932, d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101932, d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101933 q = 1) (hb : d129527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101933, d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101933, d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101934 q = 1) (hb : d129528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101934, d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101934, d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101935 q = 1) (hb : d129529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101935, d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101935, d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101936 q = 1) (hb : d129530 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101936, d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101936, d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43757 (p : Pattern) (ha : d101942 p = 1) (hb : d129536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101937 q = 1) (hb : d129531 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101937, d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101937, d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43756 q ha hb
  have h2 (q : Pattern) (ha : d101938 q = 1) (hb : d129532 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101938, d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101938, d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101939 q = 1) (hb : d129533 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101939, d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101939, d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101940 q = 1) (hb : d129534 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101940, d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101940, d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101941 q = 1) (hb : d129535 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101941, d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101941, d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101942 q = 1) (hb : d129536 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101942, d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101942, d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43758 (p : Pattern) (ha : d101949 p = 1) (hb : d129552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101945 q = 1) (hb : d129548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101945, d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101945, d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10001 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101946 q = 1) (hb : d129549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101946, d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101946, d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101947 q = 1) (hb : d129550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101947, d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101947, d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101948 q = 1) (hb : d129551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101948, d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101948, d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101949 q = 1) (hb : d129552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101949, d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101949, d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43759 (p : Pattern) (ha : d101955 p = 1) (hb : d129558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101950 q = 1) (hb : d129553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101950, d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101950, d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43758 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101951 q = 1) (hb : d129554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101951, d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101951, d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101952 q = 1) (hb : d129555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101952, d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101952, d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101953 q = 1) (hb : d129556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101953, d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101953, d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101954 q = 1) (hb : d129557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101954, d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101954, d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101955 q = 1) (hb : d129558 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101955, d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101955, d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43760 (p : Pattern) (ha : d101961 p = 1) (hb : d129564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101956 q = 1) (hb : d129559 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101956, d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101956, d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43759 q ha hb
  have h2 (q : Pattern) (ha : d101957 q = 1) (hb : d129560 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101957, d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101957, d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101958 q = 1) (hb : d129561 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101958, d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101958, d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101959 q = 1) (hb : d129562 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101959, d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101959, d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101960 q = 1) (hb : d129563 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101960, d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101960, d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101961 q = 1) (hb : d129564 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101961, d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101961, d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43761 (p : Pattern) (ha : d101969 p = 1) (hb : d129581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10176 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101965 q = 1) (hb : d129577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101965, d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101965, d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10307 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101966 q = 1) (hb : d129578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101966, d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101966, d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101967 q = 1) (hb : d129579 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101967, d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101967, d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101968 q = 1) (hb : d129580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101968, d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101968, d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101969 q = 1) (hb : d129581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101969, d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101969, d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43762 (p : Pattern) (ha : d101975 p = 1) (hb : d129587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101970 q = 1) (hb : d129582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101970, d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101970, d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43761 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10323 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101971 q = 1) (hb : d129583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101971, d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101971, d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101972 q = 1) (hb : d129584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101972, d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101972, d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101973 q = 1) (hb : d129585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101973, d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101973, d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101974 q = 1) (hb : d129586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101974, d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101974, d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101975 q = 1) (hb : d129587 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101975, d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101975, d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43763 (p : Pattern) (ha : d101981 p = 1) (hb : d129593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101976 q = 1) (hb : d129588 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101976, d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101976, d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43762 q ha hb
  have h2 (q : Pattern) (ha : d101977 q = 1) (hb : d129589 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101977, d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101977, d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101978 q = 1) (hb : d129590 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101978, d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101978, d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101979 q = 1) (hb : d129591 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101979, d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101979, d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101980 q = 1) (hb : d129592 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101980, d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101980, d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101981 q = 1) (hb : d129593 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101981, d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101981, d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43764 (p : Pattern) (ha : d101990 p = 1) (hb : d129611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129606 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101986 q = 1) (hb : d129607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101986, d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d101986, d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10573 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101987 q = 1) (hb : d129608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101987, d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101987, d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d101988 q = 1) (hb : d129609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101988, d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101988, d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101989 q = 1) (hb : d129610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101989, d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101989, d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101990 q = 1) (hb : d129611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101990, d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101990, d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43765 (p : Pattern) (ha : d101996 p = 1) (hb : d129617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101991 q = 1) (hb : d129612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101991, d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101991, d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43764 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101992 q = 1) (hb : d129613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101992, d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101992, d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d101993 q = 1) (hb : d129614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101993, d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101993, d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101994 q = 1) (hb : d129615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101994, d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101994, d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101995 q = 1) (hb : d129616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101995, d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101995, d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101996 q = 1) (hb : d129617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101996, d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101996, d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43766 (p : Pattern) (ha : d102002 p = 1) (hb : d129623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101997 q = 1) (hb : d129618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101997, d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101997, d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43765 q ha hb
  have h2 (q : Pattern) (ha : d101998 q = 1) (hb : d129619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101998, d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101998, d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101999 q = 1) (hb : d129620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101999, d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101999, d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102000 q = 1) (hb : d129621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102000, d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102000, d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102001 q = 1) (hb : d129622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102001, d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102001, d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102002 q = 1) (hb : d129623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d102002, d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102002, d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43767 (p : Pattern) (ha : d102008 p = 1) (hb : d129629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d101925 q = 1) (hb : d129518 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101925, d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43751 q ha hb
    | true =>
      simp only [d101925, d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43754 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101943 q = 1) (hb : d129537 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101943, d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101943, d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43757 q ha hb
  have h3 (q : Pattern) (ha : d101944 q = 1) (hb : d129538 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101944, d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101944, d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101962 q = 1) (hb : d129565 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101962, d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101962, d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43760 q ha hb
  have h5 (q : Pattern) (ha : d101963 q = 1) (hb : d129566 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101963, d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101963, d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101964 q = 1) (hb : d129567 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101964, d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101964, d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101982 q = 1) (hb : d129594 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101982, d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101982, d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43763 q ha hb
  have h8 (q : Pattern) (ha : d101983 q = 1) (hb : d129595 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101983, d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101983, d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101984 q = 1) (hb : d129596 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101984, d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101984, d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101985 q = 1) (hb : d129597 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101985, d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101985, d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102003 q = 1) (hb : d129624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d102003, d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102003, d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43766 q ha hb
  have h12 (q : Pattern) (ha : d102004 q = 1) (hb : d129625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d102004, d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102004, d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102005 q = 1) (hb : d129626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d102005, d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102005, d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102006 q = 1) (hb : d129627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d102006, d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102006, d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102007 q = 1) (hb : d129628 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d102007, d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d102007, d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102008 q = 1) (hb : d129629 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d102008, d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d102008, d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro43768 (p : Pattern) (ha : d102014 p = 1) (hb : d129635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102009 q = 1) (hb : d129630 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d102009, d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43767 q ha hb
    | true =>
      simp only [d102009, d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102010 q = 1) (hb : d129631 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d102010, d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102010, d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102011 q = 1) (hb : d129632 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d102011, d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102011, d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102012 q = 1) (hb : d129633 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d102012, d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102012, d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102013 q = 1) (hb : d129634 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d102013, d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102013, d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102014 q = 1) (hb : d129635 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d102014, d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102014, d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43769 (p : Pattern) (ha : d102020 p = 1) (hb : d129641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102015 q = 1) (hb : d129636 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d102015, d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43768 q ha hb
    | true =>
      simp only [d102015, d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102016 q = 1) (hb : d129637 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d102016, d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102016, d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102017 q = 1) (hb : d129638 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d102017, d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102017, d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102018 q = 1) (hb : d129639 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d102018, d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102018, d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102019 q = 1) (hb : d129640 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d102019, d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102019, d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102020 q = 1) (hb : d129641 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d102020, d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102020, d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43770 (p : Pattern) (ha : d102026 p = 1) (hb : d129647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102021 q = 1) (hb : d129642 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d102021, d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43769 q ha hb
    | true =>
      simp only [d102021, d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102022 q = 1) (hb : d129643 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d102022, d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102022, d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102023 q = 1) (hb : d129644 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d102023, d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102023, d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102024 q = 1) (hb : d129645 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d102024, d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102024, d129645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102025 q = 1) (hb : d129646 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d102025, d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102025, d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102026 q = 1) (hb : d129647 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d102026, d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102026, d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43771 (p : Pattern) (ha : d102032 p = 1) (hb : d129653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102027 q = 1) (hb : d129648 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d102027, d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43770 q ha hb
    | true =>
      simp only [d102027, d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102028 q = 1) (hb : d129649 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d102028, d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102028, d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102029 q = 1) (hb : d129650 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d102029, d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102029, d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102030 q = 1) (hb : d129651 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d102030, d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102030, d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102031 q = 1) (hb : d129652 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d102031, d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102031, d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102032 q = 1) (hb : d129653 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d102032, d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102032, d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43772 (p : Pattern) (ha : d102038 p = 1) (hb : d129659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102033 q = 1) (hb : d129654 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102033, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43771 q ha hb
    | true =>
      simp only [d102033, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102034 q = 1) (hb : d129655 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d102034, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102034, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102035 q = 1) (hb : d129656 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d102035, d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102035, d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102036 q = 1) (hb : d129657 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d102036, d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102036, d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102037 q = 1) (hb : d129658 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d102037, d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102037, d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102038 q = 1) (hb : d129659 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d102038, d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102038, d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43773 (p : Pattern) (ha : d102044 p = 1) (hb : d129665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102039 q = 1) (hb : d129660 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d102039, d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43772 q ha hb
    | true =>
      simp only [d102039, d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102040 q = 1) (hb : d129661 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d102040, d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102040, d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102041 q = 1) (hb : d129662 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d102041, d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102041, d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102042 q = 1) (hb : d129663 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d102042, d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102042, d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102043 q = 1) (hb : d129664 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d102043, d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102043, d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102044 q = 1) (hb : d129665 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d102044, d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102044, d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43774 (p : Pattern) (ha : d102050 p = 1) (hb : d129671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102045 q = 1) (hb : d129666 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d102045, d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43773 q ha hb
    | true =>
      simp only [d102045, d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102046 q = 1) (hb : d129667 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d102046, d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102046, d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102047 q = 1) (hb : d129668 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d102047, d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102047, d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102048 q = 1) (hb : d129669 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d102048, d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102048, d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102049 q = 1) (hb : d129670 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d102049, d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102049, d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102050 q = 1) (hb : d129671 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d102050, d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102050, d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43775 (p : Pattern) (ha : d19742 p = 1) (hb : d102055 p = 1) : d189810 p = 1 := by
  have h0 (q : Pattern) (ha : d19741 q = 1) (hb : d102054 q = 1) : d19741 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9301 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19742 q = 1) (hb : d102055 q = 1) : d189810 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19742, d102055, d189810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19742, d102055, d189810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43776 (p : Pattern) (ha : d19748 p = 1) (hb : d102055 p = 1) : d189816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19743 q = 1) (hb : d102055 q = 1) : d189811 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d189811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43775 q ha hb
    | true =>
      simp only [d19743, d189811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19744 q = 1) (hb : d102055 q = 1) : d189812 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d189812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d189812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19745 q = 1) (hb : d102055 q = 1) : d189813 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19745, d189813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19745, d189813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19746 q = 1) (hb : d102055 q = 1) : d189814 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19746, d189814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19746, d189814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19747 q = 1) (hb : d102055 q = 1) : d189815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19747, d189815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19747, d189815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19748 q = 1) (hb : d102055 q = 1) : d189816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19748, d189816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19748, d189816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43777 (p : Pattern) (ha : d19754 p = 1) (hb : d102055 p = 1) : d189822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d102055 q = 1) : d189817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43776 q ha hb
    | true =>
      simp only [d19749, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19750 q = 1) (hb : d102055 q = 1) : d189818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d189818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19750, d189818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19751 q = 1) (hb : d102055 q = 1) : d189819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19751, d189819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19751, d189819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19752 q = 1) (hb : d102055 q = 1) : d189820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19752, d189820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19752, d189820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19753 q = 1) (hb : d102055 q = 1) : d189821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19753, d189821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19753, d189821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19754 q = 1) (hb : d102055 q = 1) : d189822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19754, d189822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19754, d189822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43778 (p : Pattern) (ha : d19760 p = 1) (hb : d102055 p = 1) : d189828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19755 q = 1) (hb : d102055 q = 1) : d189823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19755, d189823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19755, d189823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43777 q ha hb
  have h2 (q : Pattern) (ha : d19756 q = 1) (hb : d102055 q = 1) : d189824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d19756, d189824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19756, d189824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19757 q = 1) (hb : d102055 q = 1) : d189825 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d19757, d189825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19757, d189825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19758 q = 1) (hb : d102055 q = 1) : d189826 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d19758, d189826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19758, d189826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19759 q = 1) (hb : d102055 q = 1) : d189827 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d19759, d189827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19759, d189827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19760 q = 1) (hb : d102055 q = 1) : d189828 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d19760, d189828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19760, d189828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43779 (p : Pattern) (ha : d19769 p = 1) (hb : d102055 p = 1) : d189833 p = 1 := by
  have h0 (q : Pattern) (ha : d19768 q = 1) (hb : d102054 q = 1) : d19768 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19769 q = 1) (hb : d102055 q = 1) : d189833 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19769, d102055, d189833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19769, d102055, d189833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43780 (p : Pattern) (ha : d19775 p = 1) (hb : d102055 p = 1) : d189839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d102055 q = 1) : d189834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43779 q ha hb
    | true =>
      simp only [d19770, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d102055 q = 1) : d189835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19743 q = 1) (hb : d102055 q = 1) : d189811 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d189811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43775 q ha hb
    | true =>
      simp only [d19743, d189811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19744 q = 1) (hb : d102055 q = 1) : d189812 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d189812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d189812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19772 q = 1) (hb : d102055 q = 1) : d189836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19772, d189836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19772, d189836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19773 q = 1) (hb : d102055 q = 1) : d189837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19773, d189837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19773, d189837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19774 q = 1) (hb : d102055 q = 1) : d189838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19774, d189838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19774, d189838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19775 q = 1) (hb : d102055 q = 1) : d189839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19775, d189839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19775, d189839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43781 (p : Pattern) (ha : d102055 p = 1) (hb : d130215 p = 1) : d189845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19776 q = 1) (hb : d102055 q = 1) : d189840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d189840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43780 q ha hb
    | true =>
      simp only [d19776, d189840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43776 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130211 q = 1) : d189841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130211, d189841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130211, d189841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19749 q = 1) (hb : d102055 q = 1) : d189817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43776 q ha hb
    | true =>
      simp only [d19749, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19750 q = 1) (hb : d102055 q = 1) : d189818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d189818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19750, d189818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130212 q = 1) : d189842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130212, d189842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130212, d189842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130213 q = 1) : d189843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130213, d189843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130213, d189843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130214 q = 1) : d189844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130214, d189844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130214, d189844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130215 q = 1) : d189845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130215, d189845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130215, d189845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43782 (p : Pattern) (ha : d102055 p = 1) (hb : d130221 p = 1) : d189851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130216 q = 1) : d189846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130216, d189846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130216, d189846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43781 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130217 q = 1) : d189847 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130217, d189847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130217, d189847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130218 q = 1) : d189848 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130218, d189848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130218, d189848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130219 q = 1) : d189849 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130219, d189849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130219, d189849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130220 q = 1) : d189850 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130220, d189850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130220, d189850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130221 q = 1) : d189851 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130221, d189851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130221, d189851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43783 (p : Pattern) (ha : d19845 p = 1) (hb : d102055 p = 1) : d189881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d102055 q = 1) : d189817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43776 q ha hb
    | true =>
      simp only [d19749, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19841 q = 1) (hb : d102055 q = 1) : d189877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d189877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19841, d189877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19842 q = 1) (hb : d102055 q = 1) : d189878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d189878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19842, d189878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19843 q = 1) (hb : d102055 q = 1) : d189879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d189879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d189879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19844 q = 1) (hb : d102055 q = 1) : d189880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d189880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d189880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19845 q = 1) (hb : d102055 q = 1) : d189881 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d189881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d189881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43784 (p : Pattern) (ha : d19809 p = 1) (hb : d102055 p = 1) : d189857 p = 1 := by
  have h0 (q : Pattern) (ha : d19808 q = 1) (hb : d102054 q = 1) : d19808 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19809 q = 1) (hb : d102055 q = 1) : d189857 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19809, d102055, d189857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19809, d102055, d189857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43785 (p : Pattern) (ha : d19815 p = 1) (hb : d102055 p = 1) : d189863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19810 q = 1) (hb : d102055 q = 1) : d189858 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19810, d189858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43784 q ha hb
    | true =>
      simp only [d19810, d189858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19811 q = 1) (hb : d102055 q = 1) : d189859 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19811, d189859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19811, d189859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19770 q = 1) (hb : d102055 q = 1) : d189834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43779 q ha hb
    | true =>
      simp only [d19770, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19771 q = 1) (hb : d102055 q = 1) : d189835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19812 q = 1) (hb : d102055 q = 1) : d189860 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19812, d189860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19812, d189860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19813 q = 1) (hb : d102055 q = 1) : d189861 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19813, d189861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19813, d189861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19814 q = 1) (hb : d102055 q = 1) : d189862 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19814, d189862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19814, d189862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19815 q = 1) (hb : d102055 q = 1) : d189863 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19815, d189863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19815, d189863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43786 (p : Pattern) (ha : d19833 p = 1) (hb : d102055 p = 1) : d189869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d102055 q = 1) : d189834 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43779 q ha hb
    | true =>
      simp only [d19770, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d102055 q = 1) : d189835 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19830 q = 1) (hb : d102055 q = 1) : d189866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19830, d189866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19830, d189866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19831 q = 1) (hb : d102055 q = 1) : d189867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19831, d189867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19831, d189867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19832 q = 1) (hb : d102055 q = 1) : d189868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19832, d189868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19832, d189868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19833 q = 1) (hb : d102055 q = 1) : d189869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19833, d189869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19833, d189869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43787 (p : Pattern) (ha : d102055 p = 1) (hb : d130231 p = 1) : d189875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19816 q = 1) (hb : d102055 q = 1) : d189864 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19816, d189864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43785 q ha hb
    | true =>
      simp only [d19816, d189864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43780 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130227 q = 1) : d189865 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130227, d189865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130227, d189865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19834 q = 1) (hb : d102055 q = 1) : d189870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19834, d189870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43786 q ha hb
    | true =>
      simp only [d19834, d189870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19835 q = 1) (hb : d102055 q = 1) : d189871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19835, d189871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19835, d189871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130228 q = 1) : d189872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130228, d189872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130228, d189872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130229 q = 1) : d189873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130229, d189873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130229, d189873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130230 q = 1) : d189874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130230, d189874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130230, d189874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130231 q = 1) : d189875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130231, d189875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130231, d189875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43788 (p : Pattern) (ha : d102055 p = 1) (hb : d130237 p = 1) : d189887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130232 q = 1) : d189876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130232, d189876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130232, d189876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43787 q ha hb
  have h2 (q : Pattern) (ha : d19846 q = 1) (hb : d102055 q = 1) : d189882 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d189882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d189882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43783 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130233 q = 1) : d189883 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130233, d189883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130233, d189883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130234 q = 1) : d189884 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130234, d189884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130234, d189884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130235 q = 1) : d189885 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130235, d189885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130235, d189885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130236 q = 1) : d189886 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130236, d189886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130236, d189886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130237 q = 1) : d189887 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130237, d189887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130237, d189887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43789 (p : Pattern) (ha : d102055 p = 1) (hb : d130243 p = 1) : d189893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19761 q = 1) (hb : d102055 q = 1) : d189829 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d19761, d189829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19761, d189829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43778 q ha hb
  have h2 (q : Pattern) (ha : d19762 q = 1) (hb : d102055 q = 1) : d189830 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d19762, d189830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19762, d189830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19763 q = 1) (hb : d102055 q = 1) : d189831 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d19763, d189831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19763, d189831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19764 q = 1) (hb : d102055 q = 1) : d189832 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d19764, d189832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19764, d189832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130222 q = 1) : d189852 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130222, d189852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130222, d189852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43782 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130223 q = 1) : d189853 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130223, d189853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130223, d189853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130224 q = 1) : d189854 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130224, d189854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130224, d189854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130225 q = 1) : d189855 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130225, d189855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130225, d189855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d102055 q = 1) (hb : d130226 q = 1) : d189856 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130226, d189856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d130226, d189856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d102055 q = 1) (hb : d130238 q = 1) : d189888 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130238, d189888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130238, d189888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43788 q ha hb
  have h11 (q : Pattern) (ha : d102055 q = 1) (hb : d130239 q = 1) : d189889 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130239, d189889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130239, d189889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d102055 q = 1) (hb : d130240 q = 1) : d189890 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130240, d189890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130240, d189890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102055 q = 1) (hb : d130241 q = 1) : d189891 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130241, d189891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130241, d189891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102055 q = 1) (hb : d130242 q = 1) : d189892 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130242, d189892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130242, d189892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102055 q = 1) (hb : d130243 q = 1) : d189893 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130243, d189893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130243, d189893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43790 (p : Pattern) (ha : d19877 p = 1) (hb : d102055 p = 1) : d189904 p = 1 := by
  have h0 (q : Pattern) (ha : d19876 q = 1) (hb : d102054 q = 1) : d19876 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19877 q = 1) (hb : d102055 q = 1) : d189904 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19877, d102055, d189904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19877, d102055, d189904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43791 (p : Pattern) (ha : d19921 p = 1) (hb : d102055 p = 1) : d189927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19878 q = 1) (hb : d102055 q = 1) : d189905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d189905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43790 q ha hb
    | true =>
      simp only [d19878, d189905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19879 q = 1) (hb : d102055 q = 1) : d189906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d189906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d189906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19918 q = 1) (hb : d102055 q = 1) : d189924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19918, d189924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19918, d189924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19919 q = 1) (hb : d102055 q = 1) : d189925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19919, d189925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19919, d189925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19920 q = 1) (hb : d102055 q = 1) : d189926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19920, d189926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19920, d189926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19921 q = 1) (hb : d102055 q = 1) : d189927 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19921, d189927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19921, d189927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43792 (p : Pattern) (ha : d19927 p = 1) (hb : d102055 p = 1) : d189933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19922 q = 1) (hb : d102055 q = 1) : d189928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19922, d189928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43791 q ha hb
    | true =>
      simp only [d19922, d189928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19923 q = 1) (hb : d102055 q = 1) : d189929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19923, d189929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19923, d189929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19924 q = 1) (hb : d102055 q = 1) : d189930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19924, d189930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19924, d189930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19925 q = 1) (hb : d102055 q = 1) : d189931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19925, d189931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19925, d189931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19926 q = 1) (hb : d102055 q = 1) : d189932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19926, d189932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19926, d189932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19927 q = 1) (hb : d102055 q = 1) : d189933 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19927, d189933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19927, d189933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43793 (p : Pattern) (ha : d19864 p = 1) (hb : d102055 p = 1) : d189894 p = 1 := by
  have h0 (q : Pattern) (ha : d19863 q = 1) (hb : d102054 q = 1) : d19863 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19864 q = 1) (hb : d102055 q = 1) : d189894 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19864, d102055, d189894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19864, d102055, d189894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43794 (p : Pattern) (ha : d19869 p = 1) (hb : d102055 p = 1) : d189897 p = 1 := by
  have h0 (q : Pattern) (ha : d19868 q = 1) (hb : d102054 q = 1) : d19868 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19869 q = 1) (hb : d102055 q = 1) : d189897 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19869, d102055, d189897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19869, d102055, d189897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43795 (p : Pattern) (ha : d19875 p = 1) (hb : d102055 p = 1) : d189903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19865 q = 1) (hb : d102055 q = 1) : d189895 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19865, d189895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43793 q ha hb
    | true =>
      simp only [d19865, d189895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19866 q = 1) (hb : d102055 q = 1) : d189896 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19866, d189896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19866, d189896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19870 q = 1) (hb : d102055 q = 1) : d189898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43794 q ha hb
    | true =>
      simp only [d19870, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19871 q = 1) (hb : d102055 q = 1) : d189899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19872 q = 1) (hb : d102055 q = 1) : d189900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19872, d189900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19872, d189900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19873 q = 1) (hb : d102055 q = 1) : d189901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19873, d189901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19873, d189901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19874 q = 1) (hb : d102055 q = 1) : d189902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19874, d189902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19874, d189902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19875 q = 1) (hb : d102055 q = 1) : d189903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19875, d189903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19875, d189903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43796 (p : Pattern) (ha : d19883 p = 1) (hb : d102055 p = 1) : d189910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d102055 q = 1) : d189898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43794 q ha hb
    | true =>
      simp only [d19870, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d102055 q = 1) : d189899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19878 q = 1) (hb : d102055 q = 1) : d189905 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d189905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43790 q ha hb
    | true =>
      simp only [d19878, d189905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19879 q = 1) (hb : d102055 q = 1) : d189906 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d189906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d189906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19880 q = 1) (hb : d102055 q = 1) : d189907 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19880, d189907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19880, d189907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19881 q = 1) (hb : d102055 q = 1) : d189908 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19881, d189908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19881, d189908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19882 q = 1) (hb : d102055 q = 1) : d189909 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19882, d189909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19882, d189909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19883 q = 1) (hb : d102055 q = 1) : d189910 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19883, d189910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19883, d189910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43797 (p : Pattern) (ha : d19910 p = 1) (hb : d102055 p = 1) : d189916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d102055 q = 1) : d189898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43794 q ha hb
    | true =>
      simp only [d19870, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d102055 q = 1) : d189899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19907 q = 1) (hb : d102055 q = 1) : d189913 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19907, d189913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19907, d189913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19908 q = 1) (hb : d102055 q = 1) : d189914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19908, d189914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19908, d189914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19909 q = 1) (hb : d102055 q = 1) : d189915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19909, d189915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19909, d189915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19910 q = 1) (hb : d102055 q = 1) : d189916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19910, d189916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19910, d189916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43798 (p : Pattern) (ha : d102055 p = 1) (hb : d130248 p = 1) : d189922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19884 q = 1) (hb : d102055 q = 1) : d189911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19884, d189911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43795 q ha hb
    | true =>
      simp only [d19884, d189911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43796 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130244 q = 1) : d189912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130244, d189912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130244, d189912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19911 q = 1) (hb : d102055 q = 1) : d189917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19911, d189917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43797 q ha hb
    | true =>
      simp only [d19911, d189917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19912 q = 1) (hb : d102055 q = 1) : d189918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19912, d189918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19912, d189918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130245 q = 1) : d189919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130245, d189919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130245, d189919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130246 q = 1) : d189920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130246, d189920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130246, d189920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130247 q = 1) : d189921 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130247, d189921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130247, d189921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130248 q = 1) : d189922 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130248, d189922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130248, d189922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43799 (p : Pattern) (ha : d102055 p = 1) (hb : d130254 p = 1) : d189939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130249 q = 1) : d189923 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130249, d189923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130249, d189923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43798 q ha hb
  have h2 (q : Pattern) (ha : d19928 q = 1) (hb : d102055 q = 1) : d189934 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19928, d189934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19928, d189934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43792 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130250 q = 1) : d189935 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130250, d189935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130250, d189935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130251 q = 1) : d189936 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130251, d189936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130251, d189936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130252 q = 1) : d189937 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130252, d189937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130252, d189937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130253 q = 1) : d189938 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130253, d189938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130253, d189938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130254 q = 1) : d189939 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130254, d189939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130254, d189939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43800 (p : Pattern) (ha : d102055 p = 1) (hb : d130260 p = 1) : d189945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130255 q = 1) : d189940 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130255, d189940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130255, d189940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43799 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130256 q = 1) : d189941 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130256, d189941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130256, d189941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130257 q = 1) : d189942 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130257, d189942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130257, d189942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130258 q = 1) : d189943 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130258, d189943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130258, d189943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130259 q = 1) : d189944 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130259, d189944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130259, d189944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130260 q = 1) : d189945 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130260, d189945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130260, d189945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43801 (p : Pattern) (ha : d19965 p = 1) (hb : d102055 p = 1) : d189957 p = 1 := by
  have h0 (q : Pattern) (ha : d19964 q = 1) (hb : d102054 q = 1) : d19964 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9641 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19965 q = 1) (hb : d102055 q = 1) : d189957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19965, d102055, d189957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19965, d102055, d189957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43802 (p : Pattern) (ha : d20011 p = 1) (hb : d102055 p = 1) : d189980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19966 q = 1) (hb : d102055 q = 1) : d189958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d189958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43801 q ha hb
    | true =>
      simp only [d19966, d189958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19967 q = 1) (hb : d102055 q = 1) : d189959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d189959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d189959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20008 q = 1) (hb : d102055 q = 1) : d189977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20008, d189977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20008, d189977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20009 q = 1) (hb : d102055 q = 1) : d189978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20009, d189978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20009, d189978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20010 q = 1) (hb : d102055 q = 1) : d189979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20010, d189979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20010, d189979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20011 q = 1) (hb : d102055 q = 1) : d189980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20011, d189980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20011, d189980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43803 (p : Pattern) (ha : d20017 p = 1) (hb : d102055 p = 1) : d189986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20012 q = 1) (hb : d102055 q = 1) : d189981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20012, d189981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43802 q ha hb
    | true =>
      simp only [d20012, d189981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20013 q = 1) (hb : d102055 q = 1) : d189982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20013, d189982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20013, d189982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20014 q = 1) (hb : d102055 q = 1) : d189983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20014, d189983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20014, d189983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20015 q = 1) (hb : d102055 q = 1) : d189984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20015, d189984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20015, d189984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20016 q = 1) (hb : d102055 q = 1) : d189985 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20016, d189985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20016, d189985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20017 q = 1) (hb : d102055 q = 1) : d189986 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20017, d189986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20017, d189986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43804 (p : Pattern) (ha : d19952 p = 1) (hb : d102055 p = 1) : d189947 p = 1 := by
  have h0 (q : Pattern) (ha : d19951 q = 1) (hb : d102054 q = 1) : d19951 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9628 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19952 q = 1) (hb : d102055 q = 1) : d189947 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19952, d102055, d189947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19952, d102055, d189947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43805 (p : Pattern) (ha : d19957 p = 1) (hb : d102055 p = 1) : d189950 p = 1 := by
  have h0 (q : Pattern) (ha : d19956 q = 1) (hb : d102054 q = 1) : d19956 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9633 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19957 q = 1) (hb : d102055 q = 1) : d189950 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19957, d102055, d189950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19957, d102055, d189950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43806 (p : Pattern) (ha : d19963 p = 1) (hb : d102055 p = 1) : d189956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19953 q = 1) (hb : d102055 q = 1) : d189948 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19953, d189948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43804 q ha hb
    | true =>
      simp only [d19953, d189948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19954 q = 1) (hb : d102055 q = 1) : d189949 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19954, d189949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19954, d189949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19958 q = 1) (hb : d102055 q = 1) : d189951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43805 q ha hb
    | true =>
      simp only [d19958, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19959 q = 1) (hb : d102055 q = 1) : d189952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19960 q = 1) (hb : d102055 q = 1) : d189953 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19960, d189953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19960, d189953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19961 q = 1) (hb : d102055 q = 1) : d189954 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19961, d189954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19961, d189954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19962 q = 1) (hb : d102055 q = 1) : d189955 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19962, d189955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19962, d189955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19963 q = 1) (hb : d102055 q = 1) : d189956 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19963, d189956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19963, d189956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43807 (p : Pattern) (ha : d19971 p = 1) (hb : d102055 p = 1) : d189963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d102055 q = 1) : d189951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43805 q ha hb
    | true =>
      simp only [d19958, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d102055 q = 1) : d189952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19966 q = 1) (hb : d102055 q = 1) : d189958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d189958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43801 q ha hb
    | true =>
      simp only [d19966, d189958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19967 q = 1) (hb : d102055 q = 1) : d189959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d189959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d189959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19968 q = 1) (hb : d102055 q = 1) : d189960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19968, d189960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19968, d189960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19969 q = 1) (hb : d102055 q = 1) : d189961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19969, d189961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19969, d189961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19970 q = 1) (hb : d102055 q = 1) : d189962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19970, d189962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19970, d189962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19971 q = 1) (hb : d102055 q = 1) : d189963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19971, d189963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19971, d189963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43808 (p : Pattern) (ha : d20000 p = 1) (hb : d102055 p = 1) : d189969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d102055 q = 1) : d189951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43805 q ha hb
    | true =>
      simp only [d19958, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d102055 q = 1) : d189952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19997 q = 1) (hb : d102055 q = 1) : d189966 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19997, d189966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19997, d189966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19998 q = 1) (hb : d102055 q = 1) : d189967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19998, d189967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19998, d189967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19999 q = 1) (hb : d102055 q = 1) : d189968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19999, d189968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19999, d189968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20000 q = 1) (hb : d102055 q = 1) : d189969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20000, d189969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20000, d189969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43809 (p : Pattern) (ha : d102055 p = 1) (hb : d130266 p = 1) : d189975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19972 q = 1) (hb : d102055 q = 1) : d189964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19972, d189964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43806 q ha hb
    | true =>
      simp only [d19972, d189964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43807 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130262 q = 1) : d189965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130262, d189965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130262, d189965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20001 q = 1) (hb : d102055 q = 1) : d189970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20001, d189970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43808 q ha hb
    | true =>
      simp only [d20001, d189970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20002 q = 1) (hb : d102055 q = 1) : d189971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20002, d189971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20002, d189971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130263 q = 1) : d189972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130263, d189972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130263, d189972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130264 q = 1) : d189973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130264, d189973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130264, d189973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130265 q = 1) : d189974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130265, d189974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130265, d189974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130266 q = 1) : d189975 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130266, d189975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130266, d189975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43810 (p : Pattern) (ha : d102055 p = 1) (hb : d130272 p = 1) : d189992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130267 q = 1) : d189976 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130267, d189976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130267, d189976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43809 q ha hb
  have h2 (q : Pattern) (ha : d20018 q = 1) (hb : d102055 q = 1) : d189987 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20018, d189987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20018, d189987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43803 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130268 q = 1) : d189988 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130268, d189988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130268, d189988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130269 q = 1) : d189989 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130269, d189989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130269, d189989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130270 q = 1) : d189990 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130270, d189990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130270, d189990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130271 q = 1) : d189991 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130271, d189991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130271, d189991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130272 q = 1) : d189992 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130272, d189992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130272, d189992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43811 (p : Pattern) (ha : d102055 p = 1) (hb : d130278 p = 1) : d189998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130273 q = 1) : d189993 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130273, d189993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130273, d189993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43810 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130274 q = 1) : d189994 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130274, d189994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130274, d189994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130275 q = 1) : d189995 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130275, d189995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130275, d189995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130276 q = 1) : d189996 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130276, d189996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130276, d189996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130277 q = 1) : d189997 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130277, d189997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130277, d189997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130278 q = 1) : d189998 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130278, d189998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130278, d189998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43812 (p : Pattern) (ha : d20059 p = 1) (hb : d102055 p = 1) : d190011 p = 1 := by
  have h0 (q : Pattern) (ha : d20058 q = 1) (hb : d102054 q = 1) : d20058 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9874 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20059 q = 1) (hb : d102055 q = 1) : d190011 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20059, d102055, d190011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20059, d102055, d190011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43813 (p : Pattern) (ha : d20114 p = 1) (hb : d102055 p = 1) : d190037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20060 q = 1) (hb : d102055 q = 1) : d190012 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43812 q ha hb
    | true =>
      simp only [d20060, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20061 q = 1) (hb : d102055 q = 1) : d190013 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20111 q = 1) (hb : d102055 q = 1) : d190034 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20111, d190034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20111, d190034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20112 q = 1) (hb : d102055 q = 1) : d190035 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20112, d190035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20112, d190035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20113 q = 1) (hb : d102055 q = 1) : d190036 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20113, d190036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20113, d190036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20114 q = 1) (hb : d102055 q = 1) : d190037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20114, d190037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20114, d190037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43814 (p : Pattern) (ha : d20120 p = 1) (hb : d102055 p = 1) : d190043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20115 q = 1) (hb : d102055 q = 1) : d190038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20115, d190038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43813 q ha hb
    | true =>
      simp only [d20115, d190038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20116 q = 1) (hb : d102055 q = 1) : d190039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20116, d190039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20116, d190039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20117 q = 1) (hb : d102055 q = 1) : d190040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20117, d190040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20117, d190040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20118 q = 1) (hb : d102055 q = 1) : d190041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20118, d190041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20118, d190041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20119 q = 1) (hb : d102055 q = 1) : d190042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20119, d190042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20119, d190042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20120 q = 1) (hb : d102055 q = 1) : d190043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20120, d190043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20120, d190043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43815 (p : Pattern) (ha : d20043 p = 1) (hb : d102055 p = 1) : d190001 p = 1 := by
  have h0 (q : Pattern) (ha : d20042 q = 1) (hb : d102054 q = 1) : d20042 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20043 q = 1) (hb : d102055 q = 1) : d190001 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20043, d102055, d190001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20043, d102055, d190001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43816 (p : Pattern) (ha : d20048 p = 1) (hb : d102055 p = 1) : d190004 p = 1 := by
  have h0 (q : Pattern) (ha : d20047 q = 1) (hb : d102054 q = 1) : d20047 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20048 q = 1) (hb : d102055 q = 1) : d190004 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20048, d102055, d190004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20048, d102055, d190004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43817 (p : Pattern) (ha : d20054 p = 1) (hb : d102055 p = 1) : d190010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20044 q = 1) (hb : d102055 q = 1) : d190002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20044, d190002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43815 q ha hb
    | true =>
      simp only [d20044, d190002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20045 q = 1) (hb : d102055 q = 1) : d190003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20045, d190003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20045, d190003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20049 q = 1) (hb : d102055 q = 1) : d190005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20049, d190005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43816 q ha hb
    | true =>
      simp only [d20049, d190005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20050 q = 1) (hb : d102055 q = 1) : d190006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20050, d190006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20050, d190006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20051 q = 1) (hb : d102055 q = 1) : d190007 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20051, d190007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20051, d190007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20052 q = 1) (hb : d102055 q = 1) : d190008 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20052, d190008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20052, d190008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20053 q = 1) (hb : d102055 q = 1) : d190009 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20053, d190009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20053, d190009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20054 q = 1) (hb : d102055 q = 1) : d190010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20054, d190010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20054, d190010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43818 (p : Pattern) (ha : d20065 p = 1) (hb : d102055 p = 1) : d190017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20049 q = 1) (hb : d102055 q = 1) : d190005 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20049, d190005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43816 q ha hb
    | true =>
      simp only [d20049, d190005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20050 q = 1) (hb : d102055 q = 1) : d190006 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20050, d190006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20050, d190006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20060 q = 1) (hb : d102055 q = 1) : d190012 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43812 q ha hb
    | true =>
      simp only [d20060, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20061 q = 1) (hb : d102055 q = 1) : d190013 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20062 q = 1) (hb : d102055 q = 1) : d190014 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20062, d190014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20062, d190014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20063 q = 1) (hb : d102055 q = 1) : d190015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20063, d190015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20063, d190015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20064 q = 1) (hb : d102055 q = 1) : d190016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20064, d190016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20064, d190016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20065 q = 1) (hb : d102055 q = 1) : d190017 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20065, d190017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20065, d190017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43819 (p : Pattern) (ha : d20097 p = 1) (hb : d102055 p = 1) : d190020 p = 1 := by
  have h0 (q : Pattern) (ha : d20096 q = 1) (hb : d102054 q = 1) : d20096 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9992 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20097 q = 1) (hb : d102055 q = 1) : d190020 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20097, d102055, d190020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20097, d102055, d190020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43820 (p : Pattern) (ha : d20103 p = 1) (hb : d102055 p = 1) : d190026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20098 q = 1) (hb : d102055 q = 1) : d190021 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20098, d190021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43819 q ha hb
    | true =>
      simp only [d20098, d190021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20099 q = 1) (hb : d102055 q = 1) : d190022 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20099, d190022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20099, d190022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20100 q = 1) (hb : d102055 q = 1) : d190023 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20100, d190023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20100, d190023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20101 q = 1) (hb : d102055 q = 1) : d190024 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20101, d190024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20101, d190024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20102 q = 1) (hb : d102055 q = 1) : d190025 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20102, d190025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20102, d190025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20103 q = 1) (hb : d102055 q = 1) : d190026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20103, d190026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20103, d190026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43821 (p : Pattern) (ha : d102055 p = 1) (hb : d130285 p = 1) : d190032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20066 q = 1) (hb : d102055 q = 1) : d190018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20066, d190018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43817 q ha hb
    | true =>
      simp only [d20066, d190018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43818 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130281 q = 1) : d190019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130281, d190019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130281, d190019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20104 q = 1) (hb : d102055 q = 1) : d190027 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20104, d190027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43820 q ha hb
    | true =>
      simp only [d20104, d190027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20105 q = 1) (hb : d102055 q = 1) : d190028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20105, d190028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20105, d190028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130282 q = 1) : d190029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130282, d190029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130282, d190029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130283 q = 1) : d190030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130283, d190030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130283, d190030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130284 q = 1) : d190031 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130284, d190031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130284, d190031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130285 q = 1) : d190032 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130285, d190032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130285, d190032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43822 (p : Pattern) (ha : d102055 p = 1) (hb : d130291 p = 1) : d190049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130286 q = 1) : d190033 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130286, d190033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130286, d190033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43821 q ha hb
  have h2 (q : Pattern) (ha : d20121 q = 1) (hb : d102055 q = 1) : d190044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20121, d190044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20121, d190044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43814 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130287 q = 1) : d190045 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130287, d190045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130287, d190045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130288 q = 1) : d190046 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130288, d190046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130288, d190046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130289 q = 1) : d190047 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130289, d190047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130289, d190047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130290 q = 1) : d190048 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130290, d190048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130290, d190048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130291 q = 1) : d190049 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130291, d190049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130291, d190049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43823 (p : Pattern) (ha : d102055 p = 1) (hb : d130297 p = 1) : d190055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130292 q = 1) : d190050 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130292, d190050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130292, d190050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43822 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130293 q = 1) : d190051 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130293, d190051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130293, d190051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130294 q = 1) : d190052 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130294, d190052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130294, d190052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130295 q = 1) : d190053 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130295, d190053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130295, d190053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130296 q = 1) : d190054 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130296, d190054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130296, d190054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130297 q = 1) : d190055 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130297, d190055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130297, d190055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43824 (p : Pattern) (ha : d20163 p = 1) (hb : d102055 p = 1) : d190069 p = 1 := by
  have h0 (q : Pattern) (ha : d20162 q = 1) (hb : d102054 q = 1) : d20162 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20163 q = 1) (hb : d102055 q = 1) : d190069 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20163, d102055, d190069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20163, d102055, d190069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43825 (p : Pattern) (ha : d20218 p = 1) (hb : d102055 p = 1) : d190095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20164 q = 1) (hb : d102055 q = 1) : d190070 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43824 q ha hb
    | true =>
      simp only [d20164, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20165 q = 1) (hb : d102055 q = 1) : d190071 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20215 q = 1) (hb : d102055 q = 1) : d190092 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20215, d190092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20215, d190092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20216 q = 1) (hb : d102055 q = 1) : d190093 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20216, d190093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20216, d190093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20217 q = 1) (hb : d102055 q = 1) : d190094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20217, d190094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20217, d190094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20218 q = 1) (hb : d102055 q = 1) : d190095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20218, d190095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20218, d190095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43826 (p : Pattern) (ha : d20224 p = 1) (hb : d102055 p = 1) : d190101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20219 q = 1) (hb : d102055 q = 1) : d190096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20219, d190096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43825 q ha hb
    | true =>
      simp only [d20219, d190096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20220 q = 1) (hb : d102055 q = 1) : d190097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20220, d190097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20220, d190097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20221 q = 1) (hb : d102055 q = 1) : d190098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20221, d190098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20221, d190098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20222 q = 1) (hb : d102055 q = 1) : d190099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20222, d190099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20222, d190099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20223 q = 1) (hb : d102055 q = 1) : d190100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20223, d190100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20223, d190100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20224 q = 1) (hb : d102055 q = 1) : d190101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20224, d190101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20224, d190101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43827 (p : Pattern) (ha : d20147 p = 1) (hb : d102055 p = 1) : d190059 p = 1 := by
  have h0 (q : Pattern) (ha : d20146 q = 1) (hb : d102054 q = 1) : d20146 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20147 q = 1) (hb : d102055 q = 1) : d190059 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20147, d102055, d190059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20147, d102055, d190059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43828 (p : Pattern) (ha : d20152 p = 1) (hb : d102055 p = 1) : d190062 p = 1 := by
  have h0 (q : Pattern) (ha : d20151 q = 1) (hb : d102054 q = 1) : d20151 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10151 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20152 q = 1) (hb : d102055 q = 1) : d190062 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20152, d102055, d190062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20152, d102055, d190062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43829 (p : Pattern) (ha : d20158 p = 1) (hb : d102055 p = 1) : d190068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20148 q = 1) (hb : d102055 q = 1) : d190060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20148, d190060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43827 q ha hb
    | true =>
      simp only [d20148, d190060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20149 q = 1) (hb : d102055 q = 1) : d190061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20149, d190061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20149, d190061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20153 q = 1) (hb : d102055 q = 1) : d190063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d190063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43828 q ha hb
    | true =>
      simp only [d20153, d190063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20154 q = 1) (hb : d102055 q = 1) : d190064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d190064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20154, d190064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20155 q = 1) (hb : d102055 q = 1) : d190065 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20155, d190065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20155, d190065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20156 q = 1) (hb : d102055 q = 1) : d190066 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20156, d190066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20156, d190066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20157 q = 1) (hb : d102055 q = 1) : d190067 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20157, d190067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20157, d190067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20158 q = 1) (hb : d102055 q = 1) : d190068 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20158, d190068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20158, d190068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43830 (p : Pattern) (ha : d20169 p = 1) (hb : d102055 p = 1) : d190075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20153 q = 1) (hb : d102055 q = 1) : d190063 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d190063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43828 q ha hb
    | true =>
      simp only [d20153, d190063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20154 q = 1) (hb : d102055 q = 1) : d190064 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d190064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20154, d190064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20164 q = 1) (hb : d102055 q = 1) : d190070 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43824 q ha hb
    | true =>
      simp only [d20164, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20165 q = 1) (hb : d102055 q = 1) : d190071 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20166 q = 1) (hb : d102055 q = 1) : d190072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20166, d190072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20166, d190072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20167 q = 1) (hb : d102055 q = 1) : d190073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20167, d190073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20167, d190073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20168 q = 1) (hb : d102055 q = 1) : d190074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20168, d190074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20168, d190074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20169 q = 1) (hb : d102055 q = 1) : d190075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20169, d190075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20169, d190075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43831 (p : Pattern) (ha : d20201 p = 1) (hb : d102055 p = 1) : d190078 p = 1 := by
  have h0 (q : Pattern) (ha : d20200 q = 1) (hb : d102054 q = 1) : d20200 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20201 q = 1) (hb : d102055 q = 1) : d190078 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20201, d102055, d190078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20201, d102055, d190078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43832 (p : Pattern) (ha : d20207 p = 1) (hb : d102055 p = 1) : d190084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20202 q = 1) (hb : d102055 q = 1) : d190079 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20202, d190079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43831 q ha hb
    | true =>
      simp only [d20202, d190079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20203 q = 1) (hb : d102055 q = 1) : d190080 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20203, d190080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20203, d190080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20204 q = 1) (hb : d102055 q = 1) : d190081 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20204, d190081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20204, d190081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20205 q = 1) (hb : d102055 q = 1) : d190082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20205, d190082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20205, d190082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20206 q = 1) (hb : d102055 q = 1) : d190083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20206, d190083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20206, d190083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20207 q = 1) (hb : d102055 q = 1) : d190084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20207, d190084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20207, d190084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43833 (p : Pattern) (ha : d102055 p = 1) (hb : d130305 p = 1) : d190090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20170 q = 1) (hb : d102055 q = 1) : d190076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20170, d190076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43829 q ha hb
    | true =>
      simp only [d20170, d190076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43830 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130301 q = 1) : d190077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130301, d190077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130301, d190077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20208 q = 1) (hb : d102055 q = 1) : d190085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20208, d190085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43832 q ha hb
    | true =>
      simp only [d20208, d190085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20209 q = 1) (hb : d102055 q = 1) : d190086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20209, d190086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20209, d190086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130302 q = 1) : d190087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130302, d190087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130302, d190087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130303 q = 1) : d190088 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130303, d190088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130303, d190088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130304 q = 1) : d190089 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130304, d190089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130304, d190089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130305 q = 1) : d190090 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130305, d190090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130305, d190090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43834 (p : Pattern) (ha : d102055 p = 1) (hb : d130311 p = 1) : d190107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130306 q = 1) : d190091 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130306, d190091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130306, d190091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43833 q ha hb
  have h2 (q : Pattern) (ha : d20225 q = 1) (hb : d102055 q = 1) : d190102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20225, d190102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20225, d190102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43826 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130307 q = 1) : d190103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130307, d190103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130307, d190103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130308 q = 1) : d190104 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130308, d190104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130308, d190104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130309 q = 1) : d190105 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130309, d190105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130309, d190105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130310 q = 1) : d190106 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130310, d190106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130310, d190106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130311 q = 1) : d190107 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130311, d190107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130311, d190107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43835 (p : Pattern) (ha : d102055 p = 1) (hb : d130317 p = 1) : d190113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130312 q = 1) : d190108 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130312, d190108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130312, d190108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43834 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130313 q = 1) : d190109 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130313, d190109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130313, d190109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130314 q = 1) : d190110 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130314, d190110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130314, d190110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130315 q = 1) : d190111 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130315, d190111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130315, d190111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130316 q = 1) : d190112 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130316, d190112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130316, d190112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130317 q = 1) : d190113 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130317, d190113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130317, d190113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43836 (p : Pattern) (ha : d20268 p = 1) (hb : d102055 p = 1) : d190128 p = 1 := by
  have h0 (q : Pattern) (ha : d20267 q = 1) (hb : d102054 q = 1) : d20267 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10445 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20268 q = 1) (hb : d102055 q = 1) : d190128 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20268, d102055, d190128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20268, d102055, d190128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43837 (p : Pattern) (ha : d20323 p = 1) (hb : d102055 p = 1) : d190154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20269 q = 1) (hb : d102055 q = 1) : d190129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43836 q ha hb
    | true =>
      simp only [d20269, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20270 q = 1) (hb : d102055 q = 1) : d190130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20320 q = 1) (hb : d102055 q = 1) : d190151 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20320, d190151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20320, d190151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20321 q = 1) (hb : d102055 q = 1) : d190152 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20321, d190152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20321, d190152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20322 q = 1) (hb : d102055 q = 1) : d190153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20322, d190153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20322, d190153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20323 q = 1) (hb : d102055 q = 1) : d190154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20323, d190154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20323, d190154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43838 (p : Pattern) (ha : d20329 p = 1) (hb : d102055 p = 1) : d190160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20324 q = 1) (hb : d102055 q = 1) : d190155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20324, d190155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43837 q ha hb
    | true =>
      simp only [d20324, d190155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20325 q = 1) (hb : d102055 q = 1) : d190156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20325, d190156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20325, d190156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20326 q = 1) (hb : d102055 q = 1) : d190157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20326, d190157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20326, d190157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20327 q = 1) (hb : d102055 q = 1) : d190158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20327, d190158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20327, d190158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20328 q = 1) (hb : d102055 q = 1) : d190159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20328, d190159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20328, d190159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20329 q = 1) (hb : d102055 q = 1) : d190160 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20329, d190160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20329, d190160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43839 (p : Pattern) (ha : d20252 p = 1) (hb : d102055 p = 1) : d190118 p = 1 := by
  have h0 (q : Pattern) (ha : d20251 q = 1) (hb : d102054 q = 1) : d20251 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10423 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20252 q = 1) (hb : d102055 q = 1) : d190118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20252, d102055, d190118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20252, d102055, d190118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43840 (p : Pattern) (ha : d20257 p = 1) (hb : d102055 p = 1) : d190121 p = 1 := by
  have h0 (q : Pattern) (ha : d20256 q = 1) (hb : d102054 q = 1) : d20256 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20257 q = 1) (hb : d102055 q = 1) : d190121 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20257, d102055, d190121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20257, d102055, d190121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43841 (p : Pattern) (ha : d20263 p = 1) (hb : d102055 p = 1) : d190127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20253 q = 1) (hb : d102055 q = 1) : d190119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20253, d190119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43839 q ha hb
    | true =>
      simp only [d20253, d190119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20254 q = 1) (hb : d102055 q = 1) : d190120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20254, d190120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20254, d190120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20258 q = 1) (hb : d102055 q = 1) : d190122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d190122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43840 q ha hb
    | true =>
      simp only [d20258, d190122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20259 q = 1) (hb : d102055 q = 1) : d190123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d190123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20259, d190123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20260 q = 1) (hb : d102055 q = 1) : d190124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20260, d190124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20260, d190124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20261 q = 1) (hb : d102055 q = 1) : d190125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20261, d190125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20261, d190125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20262 q = 1) (hb : d102055 q = 1) : d190126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20262, d190126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20262, d190126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20263 q = 1) (hb : d102055 q = 1) : d190127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20263, d190127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20263, d190127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43842 (p : Pattern) (ha : d20274 p = 1) (hb : d102055 p = 1) : d190134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20258 q = 1) (hb : d102055 q = 1) : d190122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d190122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43840 q ha hb
    | true =>
      simp only [d20258, d190122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20259 q = 1) (hb : d102055 q = 1) : d190123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d190123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20259, d190123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20269 q = 1) (hb : d102055 q = 1) : d190129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43836 q ha hb
    | true =>
      simp only [d20269, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20270 q = 1) (hb : d102055 q = 1) : d190130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20271 q = 1) (hb : d102055 q = 1) : d190131 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20271, d190131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20271, d190131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20272 q = 1) (hb : d102055 q = 1) : d190132 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20272, d190132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20272, d190132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20273 q = 1) (hb : d102055 q = 1) : d190133 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20273, d190133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20273, d190133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20274 q = 1) (hb : d102055 q = 1) : d190134 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20274, d190134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20274, d190134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro43843 (p : Pattern) (ha : d20306 p = 1) (hb : d102055 p = 1) : d190137 p = 1 := by
  have h0 (q : Pattern) (ha : d20305 q = 1) (hb : d102054 q = 1) : d20305 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10564 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20306 q = 1) (hb : d102055 q = 1) : d190137 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20306, d102055, d190137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20306, d102055, d190137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro43844 (p : Pattern) (ha : d20312 p = 1) (hb : d102055 p = 1) : d190143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20307 q = 1) (hb : d102055 q = 1) : d190138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20307, d190138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43843 q ha hb
    | true =>
      simp only [d20307, d190138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20308 q = 1) (hb : d102055 q = 1) : d190139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20308, d190139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20308, d190139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20309 q = 1) (hb : d102055 q = 1) : d190140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20309, d190140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20309, d190140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20310 q = 1) (hb : d102055 q = 1) : d190141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20310, d190141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20310, d190141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20311 q = 1) (hb : d102055 q = 1) : d190142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20311, d190142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20311, d190142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20312 q = 1) (hb : d102055 q = 1) : d190143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20312, d190143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20312, d190143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro43845 (p : Pattern) (ha : d102055 p = 1) (hb : d130326 p = 1) : d190149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20275 q = 1) (hb : d102055 q = 1) : d190135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20275, d190135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43841 q ha hb
    | true =>
      simp only [d20275, d190135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43842 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130322 q = 1) : d190136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130322, d190136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130322, d190136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20313 q = 1) (hb : d102055 q = 1) : d190144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20313, d190144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43844 q ha hb
    | true =>
      simp only [d20313, d190144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20314 q = 1) (hb : d102055 q = 1) : d190145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20314, d190145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20314, d190145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130323 q = 1) : d190146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130323, d190146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130323, d190146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130324 q = 1) : d190147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130324, d190147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130324, d190147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130325 q = 1) : d190148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130325, d190148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130325, d190148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130326 q = 1) : d190149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130326, d190149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130326, d190149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43846 (p : Pattern) (ha : d102055 p = 1) (hb : d130332 p = 1) : d190166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130327 q = 1) : d190150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130327, d190150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130327, d190150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43845 q ha hb
  have h2 (q : Pattern) (ha : d20330 q = 1) (hb : d102055 q = 1) : d190161 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20330, d190161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20330, d190161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43838 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130328 q = 1) : d190162 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130328, d190162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130328, d190162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130329 q = 1) : d190163 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130329, d190163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130329, d190163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130330 q = 1) : d190164 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130330, d190164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130330, d190164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130331 q = 1) : d190165 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130331, d190165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130331, d190165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130332 q = 1) : d190166 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130332, d190166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130332, d190166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43847 (p : Pattern) (ha : d102055 p = 1) (hb : d130338 p = 1) : d190172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130333 q = 1) : d190167 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130333, d190167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130333, d190167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43846 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130334 q = 1) : d190168 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130334, d190168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130334, d190168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130335 q = 1) : d190169 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130335, d190169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130335, d190169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130336 q = 1) : d190170 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130336, d190170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130336, d190170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130337 q = 1) : d190171 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130337, d190171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130337, d190171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130338 q = 1) : d190172 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130338, d190172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130338, d190172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43848 (p : Pattern) (ha : d102055 p = 1) (hb : d130344 p = 1) : d190178 p = 1 := by
  have h0 (q : Pattern) (ha : d102055 q = 1) (hb : d130261 q = 1) : d189946 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130261, d189946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43789 q ha hb
    | true =>
      simp only [d130261, d189946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43800 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130279 q = 1) : d189999 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130279, d189999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130279, d189999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43811 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130280 q = 1) : d190000 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130280, d190000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130280, d190000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130298 q = 1) : d190056 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130298, d190056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130298, d190056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43823 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130299 q = 1) : d190057 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130299, d190057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130299, d190057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130300 q = 1) : d190058 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130300, d190058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130300, d190058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d130318 q = 1) : d190114 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130318, d190114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130318, d190114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43835 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d130319 q = 1) : d190115 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130319, d190115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130319, d190115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d102055 q = 1) (hb : d130320 q = 1) : d190116 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130320, d190116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130320, d190116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d102055 q = 1) (hb : d130321 q = 1) : d190117 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130321, d190117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130321, d190117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102055 q = 1) (hb : d130339 q = 1) : d190173 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130339, d190173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130339, d190173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43847 q ha hb
  have h12 (q : Pattern) (ha : d102055 q = 1) (hb : d130340 q = 1) : d190174 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130340, d190174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130340, d190174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102055 q = 1) (hb : d130341 q = 1) : d190175 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130341, d190175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130341, d190175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102055 q = 1) (hb : d130342 q = 1) : d190176 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130342, d190176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130342, d190176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102055 q = 1) (hb : d130343 q = 1) : d190177 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130343, d190177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130343, d190177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102055 q = 1) (hb : d130344 q = 1) : d190178 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130344, d190178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130344, d190178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43849 (p : Pattern) (ha : d102055 p = 1) (hb : d130350 p = 1) : d190184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130345 q = 1) : d190179 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130345, d190179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43848 q ha hb
    | true =>
      simp only [d130345, d190179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130346 q = 1) : d190180 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130346, d190180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130346, d190180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130347 q = 1) : d190181 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130347, d190181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130347, d190181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130348 q = 1) : d190182 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130348, d190182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130348, d190182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130349 q = 1) : d190183 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130349, d190183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130349, d190183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130350 q = 1) : d190184 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130350, d190184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130350, d190184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43850 (p : Pattern) (ha : d102055 p = 1) (hb : d130356 p = 1) : d190190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130351 q = 1) : d190185 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130351, d190185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43849 q ha hb
    | true =>
      simp only [d130351, d190185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130352 q = 1) : d190186 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130352, d190186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130352, d190186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130353 q = 1) : d190187 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130353, d190187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130353, d190187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130354 q = 1) : d190188 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130354, d190188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130354, d190188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130355 q = 1) : d190189 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130355, d190189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130355, d190189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130356 q = 1) : d190190 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130356, d190190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130356, d190190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43851 (p : Pattern) (ha : d102055 p = 1) (hb : d130362 p = 1) : d190196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130357 q = 1) : d190191 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130357, d190191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43850 q ha hb
    | true =>
      simp only [d130357, d190191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130358 q = 1) : d190192 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130358, d190192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130358, d190192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130359 q = 1) : d190193 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130359, d190193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130359, d190193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130360 q = 1) : d190194 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130360, d190194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130360, d190194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130361 q = 1) : d190195 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130361, d190195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130361, d190195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130362 q = 1) : d190196 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130362, d190196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130362, d190196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43852 (p : Pattern) (ha : d102055 p = 1) (hb : d130368 p = 1) : d190202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130363 q = 1) : d190197 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130363, d190197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43851 q ha hb
    | true =>
      simp only [d130363, d190197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130364 q = 1) : d190198 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130364, d190198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130364, d190198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130365 q = 1) : d190199 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130365, d190199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130365, d190199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130366 q = 1) : d190200 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130366, d190200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130366, d190200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130367 q = 1) : d190201 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130367, d190201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130367, d190201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130368 q = 1) : d190202 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130368, d190202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130368, d190202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43853 (p : Pattern) (ha : d102055 p = 1) (hb : d130374 p = 1) : d190208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130369 q = 1) : d190203 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130369, d190203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43852 q ha hb
    | true =>
      simp only [d130369, d190203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130370 q = 1) : d190204 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130370, d190204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130370, d190204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130371 q = 1) : d190205 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130371, d190205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130371, d190205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130372 q = 1) : d190206 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130372, d190206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130372, d190206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130373 q = 1) : d190207 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130373, d190207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130373, d190207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130374 q = 1) : d190208 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130374, d190208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130374, d190208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43854 (p : Pattern) (ha : d102055 p = 1) (hb : d130380 p = 1) : d190214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130375 q = 1) : d190209 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130375, d190209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43853 q ha hb
    | true =>
      simp only [d130375, d190209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130376 q = 1) : d190210 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130376, d190210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130376, d190210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130377 q = 1) : d190211 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130377, d190211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130377, d190211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130378 q = 1) : d190212 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130378, d190212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130378, d190212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130379 q = 1) : d190213 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130379, d190213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130379, d190213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130380 q = 1) : d190214 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130380, d190214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130380, d190214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43855 (p : Pattern) (ha : d102055 p = 1) (hb : d130386 p = 1) : d190220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d130381 q = 1) : d190215 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130381, d190215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43854 q ha hb
    | true =>
      simp only [d130381, d190215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d130382 q = 1) : d190216 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130382, d190216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130382, d190216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d130383 q = 1) : d190217 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130383, d190217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130383, d190217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d130384 q = 1) : d190218 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130384, d190218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130384, d190218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d130385 q = 1) : d190219 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130385, d190219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130385, d190219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d130386 q = 1) : d190220 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130386, d190220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130386, d190220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43856 (p : Pattern) (ha : d189325 p = 1) (hb : d189810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19738 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19739 q = 1) (hb : d189323 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d189323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d189323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19740 q = 1) (hb : d189324 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, d189324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19740, d189324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19741 q = 1) (hb : d189325 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19741, d189325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19741, d189325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d189325 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d189325 q = 1) (hb : d189810 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d189810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro43857 (p : Pattern) (ha : d189331 p = 1) (hb : d189816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189326 q = 1) (hb : d189811 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189326, d189811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43856 q ha hb
    | true =>
      simp only [d189326, d189811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189327 q = 1) (hb : d189812 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189327, d189812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189327, d189812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189328 q = 1) (hb : d189813 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189328, d189813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189328, d189813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189329 q = 1) (hb : d189814 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189329, d189814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189329, d189814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189330 q = 1) (hb : d189815 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189330, d189815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189330, d189815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189331 q = 1) (hb : d189816 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189331, d189816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189331, d189816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43858 (p : Pattern) (ha : d189337 p = 1) (hb : d189822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189332 q = 1) (hb : d189817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189332, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43857 q ha hb
    | true =>
      simp only [d189332, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189333 q = 1) (hb : d189818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189333, d189818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189333, d189818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189334 q = 1) (hb : d189819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189334, d189819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189334, d189819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189335 q = 1) (hb : d189820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189335, d189820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189335, d189820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189336 q = 1) (hb : d189821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189336, d189821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189336, d189821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189337 q = 1) (hb : d189822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189337, d189822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189337, d189822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43859 (p : Pattern) (ha : d189343 p = 1) (hb : d189828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189338 q = 1) (hb : d189823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189338, d189823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189338, d189823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43858 q ha hb
  have h2 (q : Pattern) (ha : d189339 q = 1) (hb : d189824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189339, d189824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189339, d189824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189340 q = 1) (hb : d189825 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189340, d189825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189340, d189825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189341 q = 1) (hb : d189826 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189341, d189826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189341, d189826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189342 q = 1) (hb : d189827 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189342, d189827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189342, d189827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189343 q = 1) (hb : d189828 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189343, d189828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189343, d189828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43860 (p : Pattern) (ha : d189350 p = 1) (hb : d189833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h3 (q : Pattern) (ha : d19765 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19766 q = 1) (hb : d189348 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19738 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19739 q = 1) (hb : d189323 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d189323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d189323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19767 q = 1) (hb : d189349 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, d189349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19767, d189349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19740 q = 1) (hb : d189324 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, d189324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19740, d189324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19768 q = 1) (hb : d189350 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19768, d189350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19768, d189350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d189350 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d189350 q = 1) (hb : d189833 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d189833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43861 (p : Pattern) (ha : d189356 p = 1) (hb : d189839 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189351 q = 1) (hb : d189834 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189351, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43860 q ha hb
    | true =>
      simp only [d189351, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189352 q = 1) (hb : d189835 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189352, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189352, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189326 q = 1) (hb : d189811 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189326, d189811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43856 q ha hb
    | true =>
      simp only [d189326, d189811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189327 q = 1) (hb : d189812 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189327, d189812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189327, d189812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189353 q = 1) (hb : d189836 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189353, d189836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189353, d189836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189354 q = 1) (hb : d189837 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189354, d189837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189354, d189837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189355 q = 1) (hb : d189838 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189355, d189838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189355, d189838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189356 q = 1) (hb : d189839 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189356, d189839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189356, d189839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43862 (p : Pattern) (ha : d189362 p = 1) (hb : d189845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189357 q = 1) (hb : d189840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189357, d189840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43861 q ha hb
    | true =>
      simp only [d189357, d189840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43857 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189332 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189358 q = 1) (hb : d189841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189358, d189841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189358, d189841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189332 q = 1) (hb : d189817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189332, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43857 q ha hb
    | true =>
      simp only [d189332, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189333 q = 1) (hb : d189818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189333, d189818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189333, d189818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189359 q = 1) (hb : d189842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189359, d189842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189359, d189842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189360 q = 1) (hb : d189843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189360, d189843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189360, d189843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189361 q = 1) (hb : d189844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189361, d189844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189361, d189844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189362 q = 1) (hb : d189845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189362, d189845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189362, d189845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43863 (p : Pattern) (ha : d189368 p = 1) (hb : d189851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189363 q = 1) (hb : d189846 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189363, d189846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189363, d189846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43862 q ha hb
  have h2 (q : Pattern) (ha : d189364 q = 1) (hb : d189847 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189364, d189847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189364, d189847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189365 q = 1) (hb : d189848 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189365, d189848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189365, d189848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189366 q = 1) (hb : d189849 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189366, d189849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189366, d189849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189367 q = 1) (hb : d189850 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189367, d189850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189367, d189850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189368 q = 1) (hb : d189851 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189368, d189851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189368, d189851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43864 (p : Pattern) (ha : d189376 p = 1) (hb : d189857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h3 (q : Pattern) (ha : d19805 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19806 q = 1) (hb : d189374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d189374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d189374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h7 (q : Pattern) (ha : d19765 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19766 q = 1) (hb : d189348 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19807 q = 1) (hb : d189375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d189375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19807, d189375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19738 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19739 q = 1) (hb : d189323 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d189323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d189323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19767 q = 1) (hb : d189349 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, d189349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19767, d189349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19808 q = 1) (hb : d189376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19808, d189376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19808, d189376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d189376 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d189376 q = 1) (hb : d189857 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d189857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro43865 (p : Pattern) (ha : d189382 p = 1) (hb : d189863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189377 q = 1) (hb : d189858 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189377, d189858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43864 q ha hb
    | true =>
      simp only [d189377, d189858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189378 q = 1) (hb : d189859 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189378, d189859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189378, d189859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189351 q = 1) (hb : d189834 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189351, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43860 q ha hb
    | true =>
      simp only [d189351, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189352 q = 1) (hb : d189835 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189352, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189352, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189379 q = 1) (hb : d189860 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189379, d189860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189379, d189860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189380 q = 1) (hb : d189861 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189380, d189861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189380, d189861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189381 q = 1) (hb : d189862 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189381, d189862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189381, d189862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189382 q = 1) (hb : d189863 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189382, d189863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189382, d189863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43866 (p : Pattern) (ha : d189388 p = 1) (hb : d189869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189351 q = 1) (hb : d189834 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189351, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43860 q ha hb
    | true =>
      simp only [d189351, d189834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189352 q = 1) (hb : d189835 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189352, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189352, d189835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189385 q = 1) (hb : d189866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189385, d189866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189385, d189866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189386 q = 1) (hb : d189867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189386, d189867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189386, d189867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189387 q = 1) (hb : d189868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189387, d189868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189387, d189868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189388 q = 1) (hb : d189869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189388, d189869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189388, d189869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43867 (p : Pattern) (ha : d189394 p = 1) (hb : d189875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189383 q = 1) (hb : d189864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189383, d189864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43865 q ha hb
    | true =>
      simp only [d189383, d189864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43861 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189357 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189384 q = 1) (hb : d189865 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189384, d189865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189384, d189865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189389 q = 1) (hb : d189870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189389, d189870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43866 q ha hb
    | true =>
      simp only [d189389, d189870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189390 q = 1) (hb : d189871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189390, d189871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189390, d189871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189391 q = 1) (hb : d189872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189391, d189872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189391, d189872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189392 q = 1) (hb : d189873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189392, d189873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189392, d189873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189393 q = 1) (hb : d189874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189393, d189874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189393, d189874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189394 q = 1) (hb : d189875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189394, d189875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189394, d189875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43868 (p : Pattern) (ha : d189400 p = 1) (hb : d189881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189332 q = 1) (hb : d189817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189332, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43857 q ha hb
    | true =>
      simp only [d189332, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189396 q = 1) (hb : d189877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189396, d189877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189396, d189877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189397 q = 1) (hb : d189878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189397, d189878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189397, d189878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189398 q = 1) (hb : d189879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189398, d189879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189398, d189879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189399 q = 1) (hb : d189880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189399, d189880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189399, d189880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189400 q = 1) (hb : d189881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189400, d189881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189400, d189881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43869 (p : Pattern) (ha : d189406 p = 1) (hb : d189887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189395 q = 1) (hb : d189876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189395, d189876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189395, d189876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43867 q ha hb
  have h2 (q : Pattern) (ha : d189401 q = 1) (hb : d189882 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189401, d189882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189401, d189882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43868 q ha hb
  have h3 (q : Pattern) (ha : d189402 q = 1) (hb : d189883 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189402, d189883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189402, d189883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189403 q = 1) (hb : d189884 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189403, d189884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189403, d189884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189404 q = 1) (hb : d189885 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189404, d189885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189404, d189885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189405 q = 1) (hb : d189886 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189405, d189886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189405, d189886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189406 q = 1) (hb : d189887 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189406, d189887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189406, d189887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43870 (p : Pattern) (ha : d189412 p = 1) (hb : d189893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189344 q = 1) (hb : d189829 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189344, d189829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189344, d189829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43859 q ha hb
  have h2 (q : Pattern) (ha : d189345 q = 1) (hb : d189830 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189345, d189830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189345, d189830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189346 q = 1) (hb : d189831 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189346, d189831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189346, d189831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189347 q = 1) (hb : d189832 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189347, d189832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189347, d189832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189369 q = 1) (hb : d189852 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189369, d189852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189369, d189852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43863 q ha hb
  have h6 (q : Pattern) (ha : d189370 q = 1) (hb : d189853 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189370, d189853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189370, d189853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189371 q = 1) (hb : d189854 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189371, d189854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189371, d189854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189372 q = 1) (hb : d189855 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189372, d189855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189372, d189855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189373 q = 1) (hb : d189856 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189373, d189856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189373, d189856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d189407 q = 1) (hb : d189888 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189407, d189888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189407, d189888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43869 q ha hb
  have h11 (q : Pattern) (ha : d189408 q = 1) (hb : d189889 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189408, d189889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189408, d189889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d189409 q = 1) (hb : d189890 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189409, d189890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189409, d189890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d189410 q = 1) (hb : d189891 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189410, d189891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189410, d189891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d189411 q = 1) (hb : d189892 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189411, d189892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189411, d189892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d189412 q = 1) (hb : d189893 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189412, d189893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d189412, d189893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro43871 (p : Pattern) (ha : d189416 p = 1) (hb : d189894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9475 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23274 q ha hb
    | true =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
  have h3 (q : Pattern) (ha : d19858 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19859 q = 1) (hb : d189413 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19859, d189413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19859, d189413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9479 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23275 q ha hb
  have h7 (q : Pattern) (ha : d19860 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19861 q = 1) (hb : d189414 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19861, d189414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19861, d189414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19862 q = 1) (hb : d189415 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19862, d189415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19862, d189415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h12 (q : Pattern) (ha : d19805 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19806 q = 1) (hb : d189374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d189374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d189374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h16 (q : Pattern) (ha : d19765 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19766 q = 1) (hb : d189348 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d19807 q = 1) (hb : d189375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d189375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19807, d189375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19863 q = 1) (hb : d189416 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19863, d189416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19863, d189416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d189416 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d189416 q = 1) (hb : d189894 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d189894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro43872 (p : Pattern) (ha : d189420 p = 1) (hb : d189897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h3 (q : Pattern) (ha : d19805 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19806 q = 1) (hb : d189374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d189374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d189374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h7 (q : Pattern) (ha : d19765 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19766 q = 1) (hb : d189348 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19807 q = 1) (hb : d189375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d189375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19807, d189375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19867 q = 1) (hb : d189419 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, d189419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19867, d189419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19868 q = 1) (hb : d189420 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19868, d189420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19868, d189420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d189420 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d189420 q = 1) (hb : d189897 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d189897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43873 (p : Pattern) (ha : d189426 p = 1) (hb : d189903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189417 q = 1) (hb : d189895 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189417, d189895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43871 q ha hb
    | true =>
      simp only [d189417, d189895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189418 q = 1) (hb : d189896 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189418, d189896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189418, d189896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189421 q = 1) (hb : d189898 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189421, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43872 q ha hb
    | true =>
      simp only [d189421, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189422 q = 1) (hb : d189899 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189422, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189422, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189423 q = 1) (hb : d189900 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189423, d189900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189423, d189900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189424 q = 1) (hb : d189901 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189424, d189901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189424, d189901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189425 q = 1) (hb : d189902 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189425, d189902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189425, d189902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189426 q = 1) (hb : d189903 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189426, d189903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189426, d189903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43874 (p : Pattern) (ha : d189427 p = 1) (hb : d189904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h3 (q : Pattern) (ha : d19765 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19766 q = 1) (hb : d189348 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d189348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19867 q = 1) (hb : d189419 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, d189419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19867, d189419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19876 q = 1) (hb : d189427 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19876, d189427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19876, d189427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d189427 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d189427 q = 1) (hb : d189904 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d189904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro43875 (p : Pattern) (ha : d189433 p = 1) (hb : d189910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189421 q = 1) (hb : d189898 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189421, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43872 q ha hb
    | true =>
      simp only [d189421, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189422 q = 1) (hb : d189899 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189422, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189422, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189428 q = 1) (hb : d189905 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189428, d189905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43874 q ha hb
    | true =>
      simp only [d189428, d189905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189429 q = 1) (hb : d189906 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189429, d189906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189429, d189906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189430 q = 1) (hb : d189907 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189430, d189907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189430, d189907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189431 q = 1) (hb : d189908 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189431, d189908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189431, d189908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189432 q = 1) (hb : d189909 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189432, d189909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189432, d189909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189433 q = 1) (hb : d189910 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189433, d189910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189433, d189910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43876 (p : Pattern) (ha : d189444 p = 1) (hb : d189916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189421 q = 1) (hb : d189898 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189421, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43872 q ha hb
    | true =>
      simp only [d189421, d189898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189422 q = 1) (hb : d189899 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189422, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189422, d189899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189441 q = 1) (hb : d189913 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189441, d189913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189441, d189913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189442 q = 1) (hb : d189914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189442, d189914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189442, d189914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189443 q = 1) (hb : d189915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189443, d189915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189443, d189915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189444 q = 1) (hb : d189916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189444, d189916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189444, d189916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43877 (p : Pattern) (ha : d189450 p = 1) (hb : d189922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189434 q = 1) (hb : d189911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189434, d189911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43873 q ha hb
    | true =>
      simp only [d189434, d189911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43875 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189439 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189440 q = 1) (hb : d189912 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189440, d189912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189440, d189912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189445 q = 1) (hb : d189917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189445, d189917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43876 q ha hb
    | true =>
      simp only [d189445, d189917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189446 q = 1) (hb : d189918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189446, d189918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189446, d189918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189447 q = 1) (hb : d189919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189447, d189919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189447, d189919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189448 q = 1) (hb : d189920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189448, d189920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189448, d189920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189449 q = 1) (hb : d189921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189449, d189921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189449, d189921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189450 q = 1) (hb : d189922 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189450, d189922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189450, d189922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43878 (p : Pattern) (ha : d189438 p = 1) (hb : d189927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189428 q = 1) (hb : d189905 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189428, d189905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43874 q ha hb
    | true =>
      simp only [d189428, d189905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189429 q = 1) (hb : d189906 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189429, d189906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189429, d189906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189435 q = 1) (hb : d189924 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189435, d189924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189435, d189924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189436 q = 1) (hb : d189925 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189436, d189925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189436, d189925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189437 q = 1) (hb : d189926 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189437, d189926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189437, d189926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189438 q = 1) (hb : d189927 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189438, d189927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189438, d189927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43879 (p : Pattern) (ha : d189457 p = 1) (hb : d189933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189452 q = 1) (hb : d189928 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189452, d189928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43878 q ha hb
    | true =>
      simp only [d189452, d189928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189453 q = 1) (hb : d189929 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189453, d189929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189453, d189929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189454 q = 1) (hb : d189930 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189454, d189930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189454, d189930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189455 q = 1) (hb : d189931 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189455, d189931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189455, d189931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189456 q = 1) (hb : d189932 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189456, d189932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189456, d189932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189457 q = 1) (hb : d189933 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189457, d189933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189457, d189933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43880 (p : Pattern) (ha : d189463 p = 1) (hb : d189939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189451 q = 1) (hb : d189923 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189451, d189923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189451, d189923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43877 q ha hb
  have h2 (q : Pattern) (ha : d189458 q = 1) (hb : d189934 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189458, d189934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189458, d189934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43879 q ha hb
  have h3 (q : Pattern) (ha : d189459 q = 1) (hb : d189935 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189459, d189935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189459, d189935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189460 q = 1) (hb : d189936 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189460, d189936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189460, d189936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189461 q = 1) (hb : d189937 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189461, d189937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189461, d189937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189462 q = 1) (hb : d189938 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189462, d189938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189462, d189938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189463 q = 1) (hb : d189939 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189463, d189939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189463, d189939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43881 (p : Pattern) (ha : d189469 p = 1) (hb : d189945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189464 q = 1) (hb : d189940 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189464, d189940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189464, d189940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43880 q ha hb
  have h2 (q : Pattern) (ha : d189465 q = 1) (hb : d189941 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189465, d189941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189465, d189941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189466 q = 1) (hb : d189942 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189466, d189942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189466, d189942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189467 q = 1) (hb : d189943 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189467, d189943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189467, d189943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189468 q = 1) (hb : d189944 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189468, d189944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189468, d189944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189469 q = 1) (hb : d189945 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189469, d189945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189469, d189945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43882 (p : Pattern) (ha : d189477 p = 1) (hb : d189947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9609 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23292 q ha hb
    | true =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
  have h3 (q : Pattern) (ha : d19941 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19942 q = 1) (hb : d189471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19942, d189471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19942, d189471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9614 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23294 q ha hb
  have h7 (q : Pattern) (ha : d19943 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19944 q = 1) (hb : d189472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19944, d189472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19944, d189472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19945 q = 1) (hb : d189473 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19945, d189473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19945, d189473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h12 (q : Pattern) (ha : d19946 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19947 q = 1) (hb : d189474 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, d189474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, d189474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h16 (q : Pattern) (ha : d19948 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19949 q = 1) (hb : d189475 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d189475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d189475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d19950 q = 1) (hb : d189476 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, d189476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19950, d189476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19951 q = 1) (hb : d189477 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19951, d189477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19951, d189477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d189477 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d189477 q = 1) (hb : d189947 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d189947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro43883 (p : Pattern) (ha : d189481 p = 1) (hb : d189950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h3 (q : Pattern) (ha : d19946 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19947 q = 1) (hb : d189474 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, d189474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, d189474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h7 (q : Pattern) (ha : d19948 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19949 q = 1) (hb : d189475 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d189475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d189475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19950 q = 1) (hb : d189476 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, d189476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19950, d189476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19955 q = 1) (hb : d189480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, d189480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19955, d189480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19956 q = 1) (hb : d189481 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19956, d189481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19956, d189481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d189481 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d189481 q = 1) (hb : d189950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d189950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43884 (p : Pattern) (ha : d189487 p = 1) (hb : d189956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189478 q = 1) (hb : d189948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189478, d189948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43882 q ha hb
    | true =>
      simp only [d189478, d189948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189479 q = 1) (hb : d189949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189479, d189949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189479, d189949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189482 q = 1) (hb : d189951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189482, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43883 q ha hb
    | true =>
      simp only [d189482, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189483 q = 1) (hb : d189952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189483, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189483, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189484 q = 1) (hb : d189953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189484, d189953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189484, d189953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189485 q = 1) (hb : d189954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189485, d189954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189485, d189954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189486 q = 1) (hb : d189955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189486, d189955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189486, d189955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189487 q = 1) (hb : d189956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189487, d189956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189487, d189956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43885 (p : Pattern) (ha : d189488 p = 1) (hb : d189957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h3 (q : Pattern) (ha : d19948 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19949 q = 1) (hb : d189475 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d189475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d189475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19955 q = 1) (hb : d189480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, d189480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19955, d189480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19964 q = 1) (hb : d189488 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19964, d189488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19964, d189488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d189488 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d189488 q = 1) (hb : d189957 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d189957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d189957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro43886 (p : Pattern) (ha : d189494 p = 1) (hb : d189963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189482 q = 1) (hb : d189951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189482, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43883 q ha hb
    | true =>
      simp only [d189482, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189483 q = 1) (hb : d189952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189483, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189483, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189489 q = 1) (hb : d189958 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189489, d189958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43885 q ha hb
    | true =>
      simp only [d189489, d189958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189490 q = 1) (hb : d189959 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189490, d189959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189490, d189959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189491 q = 1) (hb : d189960 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189491, d189960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189491, d189960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189492 q = 1) (hb : d189961 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189492, d189961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189492, d189961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189493 q = 1) (hb : d189962 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189493, d189962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189493, d189962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189494 q = 1) (hb : d189963 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189494, d189963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189494, d189963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43887 (p : Pattern) (ha : d189505 p = 1) (hb : d189969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189482 q = 1) (hb : d189951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189482, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43883 q ha hb
    | true =>
      simp only [d189482, d189951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189483 q = 1) (hb : d189952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189483, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189483, d189952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189502 q = 1) (hb : d189966 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189502, d189966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189502, d189966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189503 q = 1) (hb : d189967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189503, d189967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189503, d189967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189504 q = 1) (hb : d189968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189504, d189968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189504, d189968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189505 q = 1) (hb : d189969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189505, d189969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189505, d189969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43888 (p : Pattern) (ha : d189511 p = 1) (hb : d189975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189495 q = 1) (hb : d189964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189495, d189964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43884 q ha hb
    | true =>
      simp only [d189495, d189964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43886 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189501 q = 1) (hb : d189965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189501, d189965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189501, d189965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189506 q = 1) (hb : d189970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189506, d189970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43887 q ha hb
    | true =>
      simp only [d189506, d189970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189507 q = 1) (hb : d189971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189507, d189971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189507, d189971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189508 q = 1) (hb : d189972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189508, d189972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189508, d189972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189509 q = 1) (hb : d189973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189509, d189973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189509, d189973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189510 q = 1) (hb : d189974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189510, d189974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189510, d189974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189511 q = 1) (hb : d189975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189511, d189975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189511, d189975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43889 (p : Pattern) (ha : d189499 p = 1) (hb : d189980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189489 q = 1) (hb : d189958 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189489, d189958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43885 q ha hb
    | true =>
      simp only [d189489, d189958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189490 q = 1) (hb : d189959 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189490, d189959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189490, d189959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189496 q = 1) (hb : d189977 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189496, d189977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189496, d189977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189497 q = 1) (hb : d189978 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189497, d189978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189497, d189978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189498 q = 1) (hb : d189979 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189498, d189979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189498, d189979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189499 q = 1) (hb : d189980 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189499, d189980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189499, d189980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43890 (p : Pattern) (ha : d189518 p = 1) (hb : d189986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189513 q = 1) (hb : d189981 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189513, d189981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43889 q ha hb
    | true =>
      simp only [d189513, d189981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189514 q = 1) (hb : d189982 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189514, d189982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189514, d189982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189515 q = 1) (hb : d189983 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189515, d189983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189515, d189983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189516 q = 1) (hb : d189984 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189516, d189984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189516, d189984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189517 q = 1) (hb : d189985 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189517, d189985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189517, d189985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189518 q = 1) (hb : d189986 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189518, d189986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189518, d189986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43891 (p : Pattern) (ha : d189524 p = 1) (hb : d189992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189512 q = 1) (hb : d189976 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189512, d189976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189512, d189976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43888 q ha hb
  have h2 (q : Pattern) (ha : d189519 q = 1) (hb : d189987 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189519, d189987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189519, d189987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43890 q ha hb
  have h3 (q : Pattern) (ha : d189520 q = 1) (hb : d189988 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189520, d189988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189520, d189988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189521 q = 1) (hb : d189989 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189521, d189989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189521, d189989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189522 q = 1) (hb : d189990 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189522, d189990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189522, d189990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189523 q = 1) (hb : d189991 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189523, d189991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189523, d189991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189524 q = 1) (hb : d189992 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189524, d189992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189524, d189992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43892 (p : Pattern) (ha : d189530 p = 1) (hb : d189998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189525 q = 1) (hb : d189993 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189525, d189993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189525, d189993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43891 q ha hb
  have h2 (q : Pattern) (ha : d189526 q = 1) (hb : d189994 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189526, d189994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189526, d189994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189527 q = 1) (hb : d189995 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189527, d189995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189527, d189995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189528 q = 1) (hb : d189996 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189528, d189996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189528, d189996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189529 q = 1) (hb : d189997 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189529, d189997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189529, d189997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189530 q = 1) (hb : d189998 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189530, d189998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189530, d189998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43893 (p : Pattern) (ha : d189539 p = 1) (hb : d190001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9807 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23314 q ha hb
    | true =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
  have h3 (q : Pattern) (ha : d20032 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20033 q = 1) (hb : d189533 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20033, d189533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20033, d189533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9822 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23318 q ha hb
  have h7 (q : Pattern) (ha : d20034 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20035 q = 1) (hb : d189534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20035, d189534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20035, d189534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20036 q = 1) (hb : d189535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20036, d189535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20036, d189535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h12 (q : Pattern) (ha : d20037 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20038 q = 1) (hb : d189536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d189536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d189536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h16 (q : Pattern) (ha : d20039 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20040 q = 1) (hb : d189537 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d189537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d189537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d20041 q = 1) (hb : d189538 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d189538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20041, d189538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20042 q = 1) (hb : d189539 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20042, d189539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20042, d189539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d189539 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d189539 q = 1) (hb : d190001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d190001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro43894 (p : Pattern) (ha : d189543 p = 1) (hb : d190004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h3 (q : Pattern) (ha : d20037 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20038 q = 1) (hb : d189536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d189536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d189536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h7 (q : Pattern) (ha : d20039 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20040 q = 1) (hb : d189537 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d189537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d189537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20041 q = 1) (hb : d189538 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d189538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20041, d189538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20046 q = 1) (hb : d189542 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20046, d189542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20046, d189542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20047 q = 1) (hb : d189543 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20047, d189543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20047, d189543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d189543 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d189543 q = 1) (hb : d190004 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d190004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43895 (p : Pattern) (ha : d189549 p = 1) (hb : d190010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189540 q = 1) (hb : d190002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189540, d190002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43893 q ha hb
    | true =>
      simp only [d189540, d190002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189541 q = 1) (hb : d190003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189541, d190003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189541, d190003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189544 q = 1) (hb : d190005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189544, d190005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43894 q ha hb
    | true =>
      simp only [d189544, d190005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189545 q = 1) (hb : d190006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189545, d190006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189545, d190006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189546 q = 1) (hb : d190007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189546, d190007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189546, d190007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189547 q = 1) (hb : d190008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189547, d190008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189547, d190008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189548 q = 1) (hb : d190009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189548, d190009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189548, d190009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189549 q = 1) (hb : d190010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189549, d190010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189549, d190010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43896 (p : Pattern) (ha : d189552 p = 1) (hb : d190011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h3 (q : Pattern) (ha : d20055 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20056 q = 1) (hb : d189550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, d189550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, d189550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20057 q = 1) (hb : d189551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, d189551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20057, d189551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20058 q = 1) (hb : d189552 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20058, d189552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20058, d189552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d189552 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d189552 q = 1) (hb : d190011 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d190011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro43897 (p : Pattern) (ha : d189558 p = 1) (hb : d190017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189544 q = 1) (hb : d190005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189544, d190005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43894 q ha hb
    | true =>
      simp only [d189544, d190005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189545 q = 1) (hb : d190006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189545, d190006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189545, d190006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189553 q = 1) (hb : d190012 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189553, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43896 q ha hb
    | true =>
      simp only [d189553, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189554 q = 1) (hb : d190013 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189554, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189554, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189555 q = 1) (hb : d190014 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189555, d190014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189555, d190014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189556 q = 1) (hb : d190015 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189556, d190015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189556, d190015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189557 q = 1) (hb : d190016 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189557, d190016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189557, d190016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189558 q = 1) (hb : d190017 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189558, d190017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189558, d190017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43898 (p : Pattern) (ha : d189575 p = 1) (hb : d190020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h3 (q : Pattern) (ha : d20037 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20038 q = 1) (hb : d189536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d189536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d189536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h7 (q : Pattern) (ha : d20039 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20040 q = 1) (hb : d189537 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d189537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d189537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20041 q = 1) (hb : d189538 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d189538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20041, d189538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9988 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23324 q ha hb
  have h12 (q : Pattern) (ha : d20093 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20094 q = 1) (hb : d189573 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20094, d189573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20094, d189573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20095 q = 1) (hb : d189574 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20095, d189574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20095, d189574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20096 q = 1) (hb : d189575 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20096, d189575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20096, d189575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d189575 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d189575 q = 1) (hb : d190020 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d190020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro43899 (p : Pattern) (ha : d189581 p = 1) (hb : d190026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189576 q = 1) (hb : d190021 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189576, d190021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43898 q ha hb
    | true =>
      simp only [d189576, d190021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189577 q = 1) (hb : d190022 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189577, d190022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189577, d190022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189578 q = 1) (hb : d190023 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189578, d190023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189578, d190023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189579 q = 1) (hb : d190024 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189579, d190024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189579, d190024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189580 q = 1) (hb : d190025 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189580, d190025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189580, d190025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189581 q = 1) (hb : d190026 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189581, d190026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189581, d190026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43900 (p : Pattern) (ha : d189587 p = 1) (hb : d190032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189559 q = 1) (hb : d190018 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189559, d190018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43895 q ha hb
    | true =>
      simp only [d189559, d190018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43897 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189572 q = 1) (hb : d190019 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189572, d190019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189572, d190019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189582 q = 1) (hb : d190027 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189582, d190027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43899 q ha hb
    | true =>
      simp only [d189582, d190027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189583 q = 1) (hb : d190028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189583, d190028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189583, d190028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189584 q = 1) (hb : d190029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189584, d190029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189584, d190029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189585 q = 1) (hb : d190030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189585, d190030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189585, d190030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189586 q = 1) (hb : d190031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189586, d190031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189586, d190031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189587 q = 1) (hb : d190032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189587, d190032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189587, d190032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43901 (p : Pattern) (ha : d189570 p = 1) (hb : d190037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189553 q = 1) (hb : d190012 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189553, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43896 q ha hb
    | true =>
      simp only [d189553, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189554 q = 1) (hb : d190013 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189554, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189554, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189567 q = 1) (hb : d190034 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189567, d190034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189567, d190034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189568 q = 1) (hb : d190035 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189568, d190035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189568, d190035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189569 q = 1) (hb : d190036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189569, d190036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189569, d190036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189570 q = 1) (hb : d190037 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189570, d190037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189570, d190037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43902 (p : Pattern) (ha : d189594 p = 1) (hb : d190043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189589 q = 1) (hb : d190038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189589, d190038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43901 q ha hb
    | true =>
      simp only [d189589, d190038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189590 q = 1) (hb : d190039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189590, d190039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189590, d190039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189591 q = 1) (hb : d190040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189591, d190040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189591, d190040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189592 q = 1) (hb : d190041 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189592, d190041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189592, d190041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189593 q = 1) (hb : d190042 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189593, d190042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189593, d190042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189594 q = 1) (hb : d190043 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189594, d190043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189594, d190043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43903 (p : Pattern) (ha : d189600 p = 1) (hb : d190049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189588 q = 1) (hb : d190033 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189588, d190033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189588, d190033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43900 q ha hb
  have h2 (q : Pattern) (ha : d189595 q = 1) (hb : d190044 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189595, d190044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189595, d190044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43902 q ha hb
  have h3 (q : Pattern) (ha : d189596 q = 1) (hb : d190045 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189596, d190045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189596, d190045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189597 q = 1) (hb : d190046 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189597, d190046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189597, d190046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189598 q = 1) (hb : d190047 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189598, d190047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189598, d190047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189599 q = 1) (hb : d190048 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189599, d190048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189599, d190048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189600 q = 1) (hb : d190049 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189600, d190049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189600, d190049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43904 (p : Pattern) (ha : d189606 p = 1) (hb : d190055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189601 q = 1) (hb : d190050 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189601, d190050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189601, d190050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43903 q ha hb
  have h2 (q : Pattern) (ha : d189602 q = 1) (hb : d190051 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189602, d190051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189602, d190051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189603 q = 1) (hb : d190052 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189603, d190052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189603, d190052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189604 q = 1) (hb : d190053 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189604, d190053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189604, d190053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189605 q = 1) (hb : d190054 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189605, d190054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189605, d190054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189606 q = 1) (hb : d190055 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189606, d190055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189606, d190055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43905 (p : Pattern) (ha : d189616 p = 1) (hb : d190059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10092 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23342 q ha hb
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
  have h3 (q : Pattern) (ha : d20136 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20137 q = 1) (hb : d189610 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20137, d189610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20137, d189610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10107 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23346 q ha hb
  have h7 (q : Pattern) (ha : d20138 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20139 q = 1) (hb : d189611 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20139, d189611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20139, d189611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20140 q = 1) (hb : d189612 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20140, d189612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20140, d189612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h12 (q : Pattern) (ha : d20141 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20142 q = 1) (hb : d189613 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d189613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d189613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h16 (q : Pattern) (ha : d20143 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20144 q = 1) (hb : d189614 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d189614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d189614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d20145 q = 1) (hb : d189615 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d189615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20145, d189615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20146 q = 1) (hb : d189616 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20146, d189616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20146, d189616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d189616 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d189616 q = 1) (hb : d190059 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d190059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro43906 (p : Pattern) (ha : d189620 p = 1) (hb : d190062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h3 (q : Pattern) (ha : d20141 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20142 q = 1) (hb : d189613 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d189613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d189613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h7 (q : Pattern) (ha : d20143 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20144 q = 1) (hb : d189614 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d189614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d189614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20145 q = 1) (hb : d189615 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d189615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20145, d189615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20150 q = 1) (hb : d189619 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20150, d189619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20150, d189619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20151 q = 1) (hb : d189620 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20151, d189620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20151, d189620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d189620 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d189620 q = 1) (hb : d190062 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d190062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43907 (p : Pattern) (ha : d189626 p = 1) (hb : d190068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189617 q = 1) (hb : d190060 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189617, d190060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43905 q ha hb
    | true =>
      simp only [d189617, d190060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189618 q = 1) (hb : d190061 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189618, d190061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189618, d190061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189621 q = 1) (hb : d190063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189621, d190063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43906 q ha hb
    | true =>
      simp only [d189621, d190063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189622 q = 1) (hb : d190064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189622, d190064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189622, d190064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189623 q = 1) (hb : d190065 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189623, d190065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189623, d190065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189624 q = 1) (hb : d190066 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189624, d190066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189624, d190066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189625 q = 1) (hb : d190067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189625, d190067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189625, d190067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189626 q = 1) (hb : d190068 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189626, d190068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189626, d190068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43908 (p : Pattern) (ha : d189629 p = 1) (hb : d190069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h3 (q : Pattern) (ha : d20159 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20160 q = 1) (hb : d189627 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, d189627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20160, d189627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20161 q = 1) (hb : d189628 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, d189628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20161, d189628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20162 q = 1) (hb : d189629 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20162, d189629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20162, d189629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d189629 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d189629 q = 1) (hb : d190069 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d190069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro43909 (p : Pattern) (ha : d189635 p = 1) (hb : d190075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189621 q = 1) (hb : d190063 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189621, d190063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43906 q ha hb
    | true =>
      simp only [d189621, d190063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189622 q = 1) (hb : d190064 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189622, d190064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189622, d190064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189630 q = 1) (hb : d190070 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189630, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43908 q ha hb
    | true =>
      simp only [d189630, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189631 q = 1) (hb : d190071 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189631, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189631, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189632 q = 1) (hb : d190072 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189632, d190072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189632, d190072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189633 q = 1) (hb : d190073 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189633, d190073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189633, d190073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189634 q = 1) (hb : d190074 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189634, d190074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189634, d190074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189635 q = 1) (hb : d190075 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189635, d190075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189635, d190075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43910 (p : Pattern) (ha : d189652 p = 1) (hb : d190078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h3 (q : Pattern) (ha : d20141 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20142 q = 1) (hb : d189613 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d189613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d189613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h7 (q : Pattern) (ha : d20143 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20144 q = 1) (hb : d189614 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d189614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d189614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20145 q = 1) (hb : d189615 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d189615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20145, d189615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10294 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23352 q ha hb
  have h12 (q : Pattern) (ha : d20197 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20198 q = 1) (hb : d189650 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20198, d189650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20198, d189650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20199 q = 1) (hb : d189651 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20199, d189651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20199, d189651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20200 q = 1) (hb : d189652 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20200, d189652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20200, d189652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d189652 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d189652 q = 1) (hb : d190078 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d190078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro43911 (p : Pattern) (ha : d189658 p = 1) (hb : d190084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189653 q = 1) (hb : d190079 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189653, d190079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43910 q ha hb
    | true =>
      simp only [d189653, d190079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189654 q = 1) (hb : d190080 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189654, d190080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189654, d190080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189655 q = 1) (hb : d190081 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189655, d190081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189655, d190081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189656 q = 1) (hb : d190082 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189656, d190082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189656, d190082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189657 q = 1) (hb : d190083 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189657, d190083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189657, d190083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189658 q = 1) (hb : d190084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189658, d190084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189658, d190084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43912 (p : Pattern) (ha : d189664 p = 1) (hb : d190090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189636 q = 1) (hb : d190076 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189636, d190076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43907 q ha hb
    | true =>
      simp only [d189636, d190076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43909 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189648 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189649 q = 1) (hb : d190077 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189649, d190077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189649, d190077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189659 q = 1) (hb : d190085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189659, d190085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43911 q ha hb
    | true =>
      simp only [d189659, d190085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189660 q = 1) (hb : d190086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189660, d190086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189660, d190086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189661 q = 1) (hb : d190087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189661, d190087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189661, d190087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189662 q = 1) (hb : d190088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189662, d190088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189662, d190088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189663 q = 1) (hb : d190089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189663, d190089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189663, d190089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189664 q = 1) (hb : d190090 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189664, d190090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189664, d190090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43913 (p : Pattern) (ha : d189647 p = 1) (hb : d190095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189630 q = 1) (hb : d190070 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189630, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43908 q ha hb
    | true =>
      simp only [d189630, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189631 q = 1) (hb : d190071 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189631, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189631, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189644 q = 1) (hb : d190092 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189644, d190092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189644, d190092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189645 q = 1) (hb : d190093 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189645, d190093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189645, d190093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189646 q = 1) (hb : d190094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189646, d190094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189646, d190094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189647 q = 1) (hb : d190095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189647, d190095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189647, d190095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43914 (p : Pattern) (ha : d189671 p = 1) (hb : d190101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189666 q = 1) (hb : d190096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189666, d190096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43913 q ha hb
    | true =>
      simp only [d189666, d190096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189667 q = 1) (hb : d190097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189667, d190097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189667, d190097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189668 q = 1) (hb : d190098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189668, d190098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189668, d190098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189669 q = 1) (hb : d190099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189669, d190099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189669, d190099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189670 q = 1) (hb : d190100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189670, d190100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189670, d190100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189671 q = 1) (hb : d190101 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189671, d190101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189671, d190101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43915 (p : Pattern) (ha : d189677 p = 1) (hb : d190107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189665 q = 1) (hb : d190091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189665, d190091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189665, d190091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43912 q ha hb
  have h2 (q : Pattern) (ha : d189672 q = 1) (hb : d190102 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189672, d190102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189672, d190102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43914 q ha hb
  have h3 (q : Pattern) (ha : d189673 q = 1) (hb : d190103 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189673, d190103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189673, d190103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189674 q = 1) (hb : d190104 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189674, d190104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189674, d190104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189675 q = 1) (hb : d190105 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189675, d190105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189675, d190105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189676 q = 1) (hb : d190106 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189676, d190106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189676, d190106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189677 q = 1) (hb : d190107 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189677, d190107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189677, d190107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43916 (p : Pattern) (ha : d189683 p = 1) (hb : d190113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189678 q = 1) (hb : d190108 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189678, d190108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189678, d190108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43915 q ha hb
  have h2 (q : Pattern) (ha : d189679 q = 1) (hb : d190109 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189679, d190109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189679, d190109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189680 q = 1) (hb : d190110 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189680, d190110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189680, d190110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189681 q = 1) (hb : d190111 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189681, d190111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189681, d190111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189682 q = 1) (hb : d190112 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189682, d190112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189682, d190112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189683 q = 1) (hb : d190113 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189683, d190113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189683, d190113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43917 (p : Pattern) (ha : d189694 p = 1) (hb : d190118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10378 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23368 q ha hb
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
  have h3 (q : Pattern) (ha : d20241 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20242 q = 1) (hb : d189688 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20242, d189688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20242, d189688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10383 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23371 q ha hb
  have h7 (q : Pattern) (ha : d20243 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20244 q = 1) (hb : d189689 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20244, d189689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20244, d189689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20245 q = 1) (hb : d189690 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20245, d189690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20245, d189690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h12 (q : Pattern) (ha : d20246 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20247 q = 1) (hb : d189691 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d189691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d189691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h16 (q : Pattern) (ha : d20248 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20249 q = 1) (hb : d189692 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d189692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d189692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d20250 q = 1) (hb : d189693 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d189693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20250, d189693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20251 q = 1) (hb : d189694 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20251, d189694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20251, d189694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d0 q = 1) (hb : d189694 q = 1) : d0 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d189694 q = 1) (hb : d190118 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d190118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro43918 (p : Pattern) (ha : d189698 p = 1) (hb : d190121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h3 (q : Pattern) (ha : d20246 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20247 q = 1) (hb : d189691 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d189691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d189691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h7 (q : Pattern) (ha : d20248 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20249 q = 1) (hb : d189692 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d189692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d189692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20250 q = 1) (hb : d189693 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d189693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20250, d189693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20255 q = 1) (hb : d189697 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20255, d189697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20255, d189697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20256 q = 1) (hb : d189698 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20256, d189698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20256, d189698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d189698 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d189698 q = 1) (hb : d190121 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d190121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro43919 (p : Pattern) (ha : d189704 p = 1) (hb : d190127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189695 q = 1) (hb : d190119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189695, d190119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43917 q ha hb
    | true =>
      simp only [d189695, d190119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189696 q = 1) (hb : d190120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189696, d190120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189696, d190120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189699 q = 1) (hb : d190122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189699, d190122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43918 q ha hb
    | true =>
      simp only [d189699, d190122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189700 q = 1) (hb : d190123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189700, d190123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189700, d190123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189701 q = 1) (hb : d190124 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189701, d190124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189701, d190124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189702 q = 1) (hb : d190125 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189702, d190125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189702, d190125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189703 q = 1) (hb : d190126 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189703, d190126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189703, d190126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189704 q = 1) (hb : d190127 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189704, d190127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189704, d190127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43920 (p : Pattern) (ha : d189707 p = 1) (hb : d190128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h3 (q : Pattern) (ha : d20264 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20265 q = 1) (hb : d189705 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, d189705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20265, d189705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20266 q = 1) (hb : d189706 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, d189706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20266, d189706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20267 q = 1) (hb : d189707 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20267, d189707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20267, d189707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d189707 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d189707 q = 1) (hb : d190128 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d190128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro43921 (p : Pattern) (ha : d189713 p = 1) (hb : d190134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189699 q = 1) (hb : d190122 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189699, d190122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43918 q ha hb
    | true =>
      simp only [d189699, d190122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189700 q = 1) (hb : d190123 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189700, d190123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189700, d190123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189708 q = 1) (hb : d190129 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189708, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43920 q ha hb
    | true =>
      simp only [d189708, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189709 q = 1) (hb : d190130 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189709, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189709, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189710 q = 1) (hb : d190131 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189710, d190131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189710, d190131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189711 q = 1) (hb : d190132 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189711, d190132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189711, d190132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189712 q = 1) (hb : d190133 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189712, d190133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189712, d190133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189713 q = 1) (hb : d190134 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189713, d190134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189713, d190134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43922 (p : Pattern) (ha : d189730 p = 1) (hb : d190137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h3 (q : Pattern) (ha : d20246 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20247 q = 1) (hb : d189691 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d189691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d189691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h7 (q : Pattern) (ha : d20248 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20249 q = 1) (hb : d189692 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d189692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d189692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20250 q = 1) (hb : d189693 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d189693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20250, d189693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10560 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23377 q ha hb
  have h12 (q : Pattern) (ha : d20302 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20303 q = 1) (hb : d189728 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20303, d189728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20303, d189728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20304 q = 1) (hb : d189729 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20304, d189729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20304, d189729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20305 q = 1) (hb : d189730 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20305, d189730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20305, d189730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d189730 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d189730 q = 1) (hb : d190137 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d190137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro43923 (p : Pattern) (ha : d189736 p = 1) (hb : d190143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189731 q = 1) (hb : d190138 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189731, d190138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43922 q ha hb
    | true =>
      simp only [d189731, d190138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189732 q = 1) (hb : d190139 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189732, d190139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189732, d190139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189733 q = 1) (hb : d190140 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189733, d190140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189733, d190140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189734 q = 1) (hb : d190141 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189734, d190141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189734, d190141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189735 q = 1) (hb : d190142 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189735, d190142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189735, d190142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189736 q = 1) (hb : d190143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189736, d190143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189736, d190143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43924 (p : Pattern) (ha : d189742 p = 1) (hb : d190149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189714 q = 1) (hb : d190135 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189714, d190135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43919 q ha hb
    | true =>
      simp only [d189714, d190135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43921 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189726 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189727 q = 1) (hb : d190136 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189727, d190136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189727, d190136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189737 q = 1) (hb : d190144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189737, d190144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43923 q ha hb
    | true =>
      simp only [d189737, d190144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189738 q = 1) (hb : d190145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189738, d190145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189738, d190145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189739 q = 1) (hb : d190146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189739, d190146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189739, d190146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189740 q = 1) (hb : d190147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189740, d190147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189740, d190147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189741 q = 1) (hb : d190148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189741, d190148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189741, d190148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189742 q = 1) (hb : d190149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189742, d190149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189742, d190149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro43925 (p : Pattern) (ha : d189725 p = 1) (hb : d190154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189708 q = 1) (hb : d190129 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189708, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43920 q ha hb
    | true =>
      simp only [d189708, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189709 q = 1) (hb : d190130 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189709, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189709, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189722 q = 1) (hb : d190151 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189722, d190151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189722, d190151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189723 q = 1) (hb : d190152 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189723, d190152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189723, d190152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189724 q = 1) (hb : d190153 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189724, d190153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189724, d190153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189725 q = 1) (hb : d190154 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189725, d190154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189725, d190154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43926 (p : Pattern) (ha : d189749 p = 1) (hb : d190160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189744 q = 1) (hb : d190155 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189744, d190155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43925 q ha hb
    | true =>
      simp only [d189744, d190155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189745 q = 1) (hb : d190156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189745, d190156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189745, d190156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189746 q = 1) (hb : d190157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189746, d190157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189746, d190157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189747 q = 1) (hb : d190158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189747, d190158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189747, d190158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189748 q = 1) (hb : d190159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189748, d190159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189748, d190159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189749 q = 1) (hb : d190160 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189749, d190160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189749, d190160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43927 (p : Pattern) (ha : d189755 p = 1) (hb : d190166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189743 q = 1) (hb : d190150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189743, d190150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189743, d190150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43924 q ha hb
  have h2 (q : Pattern) (ha : d189750 q = 1) (hb : d190161 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189750, d190161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189750, d190161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43926 q ha hb
  have h3 (q : Pattern) (ha : d189751 q = 1) (hb : d190162 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189751, d190162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189751, d190162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189752 q = 1) (hb : d190163 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189752, d190163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189752, d190163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189753 q = 1) (hb : d190164 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189753, d190164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189753, d190164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189754 q = 1) (hb : d190165 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189754, d190165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189754, d190165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189755 q = 1) (hb : d190166 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189755, d190166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189755, d190166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43928 (p : Pattern) (ha : d189761 p = 1) (hb : d190172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189756 q = 1) (hb : d190167 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189756, d190167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189756, d190167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43927 q ha hb
  have h2 (q : Pattern) (ha : d189757 q = 1) (hb : d190168 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189757, d190168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189757, d190168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189758 q = 1) (hb : d190169 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189758, d190169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189758, d190169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189759 q = 1) (hb : d190170 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189759, d190170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189759, d190170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189760 q = 1) (hb : d190171 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189760, d190171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189760, d190171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189761 q = 1) (hb : d190172 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189761, d190172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189761, d190172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43929 (p : Pattern) (ha : d189767 p = 1) (hb : d190178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d189470 q = 1) (hb : d189946 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189470, d189946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43870 q ha hb
    | true =>
      simp only [d189470, d189946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43881 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189531 q = 1) (hb : d189999 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189531, d189999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189531, d189999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43892 q ha hb
  have h3 (q : Pattern) (ha : d189532 q = 1) (hb : d190000 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189532, d190000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d189532, d190000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189607 q = 1) (hb : d190056 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189607, d190056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189607, d190056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43904 q ha hb
  have h5 (q : Pattern) (ha : d189608 q = 1) (hb : d190057 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189608, d190057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189608, d190057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189609 q = 1) (hb : d190058 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189609, d190058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189609, d190058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189684 q = 1) (hb : d190114 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189684, d190114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189684, d190114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43916 q ha hb
  have h8 (q : Pattern) (ha : d189685 q = 1) (hb : d190115 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189685, d190115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189685, d190115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189686 q = 1) (hb : d190116 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189686, d190116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189686, d190116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d189687 q = 1) (hb : d190117 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d189687, d190117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189687, d190117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d189762 q = 1) (hb : d190173 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189762, d190173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189762, d190173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43928 q ha hb
  have h12 (q : Pattern) (ha : d189763 q = 1) (hb : d190174 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189763, d190174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189763, d190174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d189764 q = 1) (hb : d190175 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189764, d190175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189764, d190175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d189765 q = 1) (hb : d190176 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d189765, d190176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189765, d190176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d189766 q = 1) (hb : d190177 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d189766, d190177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d189766, d190177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d189767 q = 1) (hb : d190178 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d189767, d190178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d189767, d190178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43930 (p : Pattern) (ha : d189773 p = 1) (hb : d190184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189768 q = 1) (hb : d190179 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d189768, d190179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43929 q ha hb
    | true =>
      simp only [d189768, d190179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189769 q = 1) (hb : d190180 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d189769, d190180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189769, d190180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189770 q = 1) (hb : d190181 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d189770, d190181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189770, d190181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189771 q = 1) (hb : d190182 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d189771, d190182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189771, d190182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189772 q = 1) (hb : d190183 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d189772, d190183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189772, d190183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189773 q = 1) (hb : d190184 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d189773, d190184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189773, d190184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43931 (p : Pattern) (ha : d189779 p = 1) (hb : d190190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189774 q = 1) (hb : d190185 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d189774, d190185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43930 q ha hb
    | true =>
      simp only [d189774, d190185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189775 q = 1) (hb : d190186 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d189775, d190186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189775, d190186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189776 q = 1) (hb : d190187 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d189776, d190187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189776, d190187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189777 q = 1) (hb : d190188 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d189777, d190188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189777, d190188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189778 q = 1) (hb : d190189 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d189778, d190189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189778, d190189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189779 q = 1) (hb : d190190 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d189779, d190190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189779, d190190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43932 (p : Pattern) (ha : d189785 p = 1) (hb : d190196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189780 q = 1) (hb : d190191 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d189780, d190191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43931 q ha hb
    | true =>
      simp only [d189780, d190191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189781 q = 1) (hb : d190192 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d189781, d190192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189781, d190192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189782 q = 1) (hb : d190193 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d189782, d190193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189782, d190193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189783 q = 1) (hb : d190194 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d189783, d190194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189783, d190194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189784 q = 1) (hb : d190195 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d189784, d190195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189784, d190195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189785 q = 1) (hb : d190196 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d189785, d190196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189785, d190196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43933 (p : Pattern) (ha : d189791 p = 1) (hb : d190202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189786 q = 1) (hb : d190197 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d189786, d190197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43932 q ha hb
    | true =>
      simp only [d189786, d190197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189787 q = 1) (hb : d190198 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d189787, d190198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189787, d190198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189788 q = 1) (hb : d190199 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d189788, d190199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189788, d190199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189789 q = 1) (hb : d190200 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d189789, d190200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189789, d190200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189790 q = 1) (hb : d190201 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d189790, d190201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189790, d190201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189791 q = 1) (hb : d190202 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d189791, d190202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189791, d190202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43934 (p : Pattern) (ha : d189797 p = 1) (hb : d190208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189792 q = 1) (hb : d190203 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d189792, d190203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43933 q ha hb
    | true =>
      simp only [d189792, d190203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189793 q = 1) (hb : d190204 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d189793, d190204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189793, d190204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189794 q = 1) (hb : d190205 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d189794, d190205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189794, d190205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189795 q = 1) (hb : d190206 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d189795, d190206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189795, d190206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189796 q = 1) (hb : d190207 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d189796, d190207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189796, d190207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189797 q = 1) (hb : d190208 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d189797, d190208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189797, d190208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43935 (p : Pattern) (ha : d189803 p = 1) (hb : d190214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189798 q = 1) (hb : d190209 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d189798, d190209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43934 q ha hb
    | true =>
      simp only [d189798, d190209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189799 q = 1) (hb : d190210 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d189799, d190210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189799, d190210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189800 q = 1) (hb : d190211 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d189800, d190211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189800, d190211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189801 q = 1) (hb : d190212 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d189801, d190212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189801, d190212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189802 q = 1) (hb : d190213 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d189802, d190213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189802, d190213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189803 q = 1) (hb : d190214 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d189803, d190214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189803, d190214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43936 (p : Pattern) (ha : d189809 p = 1) (hb : d190220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189804 q = 1) (hb : d190215 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d189804, d190215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43935 q ha hb
    | true =>
      simp only [d189804, d190215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189805 q = 1) (hb : d190216 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d189805, d190216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189805, d190216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189806 q = 1) (hb : d190217 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d189806, d190217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189806, d190217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189807 q = 1) (hb : d190218 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d189807, d190218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189807, d190218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189808 q = 1) (hb : d190219 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d189808, d190219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189808, d190219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189809 q = 1) (hb : d190220 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d189809, d190220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189809, d190220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43937 (p : Pattern) (ha : d102055 p = 1) (hb : d188529 p = 1) : d190225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19846 q = 1) (hb : d102055 q = 1) : d189882 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d189882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d189882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43783 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188525 q = 1) : d190221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188525, d190221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188525, d190221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188526 q = 1) : d190222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188526, d190222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188526, d190222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188527 q = 1) : d190223 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188527, d190223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188527, d190223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188528 q = 1) : d190224 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188528, d190224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188528, d190224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188529 q = 1) : d190225 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188529, d190225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188529, d190225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43938 (p : Pattern) (ha : d102055 p = 1) (hb : d188539 p = 1) : d190235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19776 q = 1) (hb : d102055 q = 1) : d189840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d189840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43780 q ha hb
    | true =>
      simp only [d19776, d189840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43776 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188535 q = 1) : d190231 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188535, d190231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188535, d190231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188536 q = 1) : d190232 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188536, d190232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188536, d190232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188537 q = 1) : d190233 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188537, d190233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188537, d190233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188538 q = 1) : d190234 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188538, d190234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188538, d190234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188539 q = 1) : d190235 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188539, d190235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188539, d190235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43939 (p : Pattern) (ha : d102055 p = 1) (hb : d188545 p = 1) : d190241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188540 q = 1) : d190236 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188540, d190236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188540, d190236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43938 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188541 q = 1) : d190237 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188541, d190237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188541, d190237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188542 q = 1) : d190238 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188542, d190238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188542, d190238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188543 q = 1) : d190239 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188543, d190239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188543, d190239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188544 q = 1) : d190240 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188544, d190240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188544, d190240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188545 q = 1) : d190241 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188545, d190241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188545, d190241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43940 (p : Pattern) (ha : d102055 p = 1) (hb : d188551 p = 1) : d190247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188530 q = 1) : d190226 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188530, d190226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188530, d190226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43937 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188531 q = 1) : d190227 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188531, d190227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188531, d190227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188532 q = 1) : d190228 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188532, d190228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188532, d190228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188533 q = 1) : d190229 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188533, d190229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188533, d190229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188534 q = 1) : d190230 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188534, d190230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188534, d190230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188546 q = 1) : d190242 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188546, d190242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188546, d190242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43939 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d188547 q = 1) : d190243 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188547, d190243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188547, d190243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d188548 q = 1) : d190244 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188548, d190244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188548, d190244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d102055 q = 1) (hb : d188549 q = 1) : d190245 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188549, d190245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188549, d190245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d102055 q = 1) (hb : d188550 q = 1) : d190246 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188550, d190246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188550, d190246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102055 q = 1) (hb : d188551 q = 1) : d190247 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188551, d190247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188551, d190247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro43941 (p : Pattern) (ha : d102055 p = 1) (hb : d188557 p = 1) : d190253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188552 q = 1) : d190248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188552, d190248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43796 q hb ha
    | true =>
      simp only [d188552, d190248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43791 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188553 q = 1) : d190249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188553, d190249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188553, d190249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188554 q = 1) : d190250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188554, d190250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188554, d190250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188555 q = 1) : d190251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188555, d190251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188555, d190251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188556 q = 1) : d190252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188556, d190252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188556, d190252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188557 q = 1) : d190253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188557, d190253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188557, d190253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43942 (p : Pattern) (ha : d102055 p = 1) (hb : d188563 p = 1) : d190259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188558 q = 1) : d190254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188558, d190254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188558, d190254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43941 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188559 q = 1) : d190255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188559, d190255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188559, d190255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188560 q = 1) : d190256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188560, d190256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188560, d190256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188561 q = 1) : d190257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188561, d190257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188561, d190257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188562 q = 1) : d190258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188562, d190258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188562, d190258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188563 q = 1) : d190259 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188563, d190259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188563, d190259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43943 (p : Pattern) (ha : d102055 p = 1) (hb : d188569 p = 1) : d190265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188564 q = 1) : d190260 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188564, d190260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188564, d190260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43942 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188565 q = 1) : d190261 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188565, d190261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188565, d190261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188566 q = 1) : d190262 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188566, d190262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188566, d190262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188567 q = 1) : d190263 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188567, d190263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188567, d190263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188568 q = 1) : d190264 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188568, d190264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188568, d190264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188569 q = 1) : d190265 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188569, d190265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188569, d190265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43944 (p : Pattern) (ha : d102055 p = 1) (hb : d188576 p = 1) : d190272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188571 q = 1) : d190267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188571, d190267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43807 q hb ha
    | true =>
      simp only [d188571, d190267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43802 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188572 q = 1) : d190268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188572, d190268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188572, d190268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188573 q = 1) : d190269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188573, d190269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188573, d190269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188574 q = 1) : d190270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188574, d190270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188574, d190270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188575 q = 1) : d190271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188575, d190271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188575, d190271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188576 q = 1) : d190272 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188576, d190272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188576, d190272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43945 (p : Pattern) (ha : d102055 p = 1) (hb : d188582 p = 1) : d190278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188577 q = 1) : d190273 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188577, d190273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188577, d190273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43944 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188578 q = 1) : d190274 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188578, d190274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188578, d190274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188579 q = 1) : d190275 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188579, d190275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188579, d190275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188580 q = 1) : d190276 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188580, d190276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188580, d190276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188581 q = 1) : d190277 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188581, d190277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188581, d190277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188582 q = 1) : d190278 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188582, d190278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188582, d190278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43946 (p : Pattern) (ha : d102055 p = 1) (hb : d188588 p = 1) : d190284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188583 q = 1) : d190279 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188583, d190279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188583, d190279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43945 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188584 q = 1) : d190280 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188584, d190280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188584, d190280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188585 q = 1) : d190281 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188585, d190281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188585, d190281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188586 q = 1) : d190282 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188586, d190282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188586, d190282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188587 q = 1) : d190283 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188587, d190283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188587, d190283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188588 q = 1) : d190284 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188588, d190284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188588, d190284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43947 (p : Pattern) (ha : d102055 p = 1) (hb : d188592 p = 1) : d190287 p = 1 := by
  have h0 (q : Pattern) (ha : d102054 q = 1) (hb : d188591 q = 1) : d188591 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188592 q = 1) : d190287 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d102055, d188592, d190287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102055, d188592, d190287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro43948 (p : Pattern) (ha : d102055 p = 1) (hb : d188598 p = 1) : d190293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188593 q = 1) : d190288 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188593, d190288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43947 q ha hb
    | true =>
      simp only [d188593, d190288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188594 q = 1) : d190289 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188594, d190289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188594, d190289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20060 q = 1) (hb : d102055 q = 1) : d190012 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43812 q ha hb
    | true =>
      simp only [d20060, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20061 q = 1) (hb : d102055 q = 1) : d190013 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188595 q = 1) : d190290 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188595, d190290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188595, d190290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188596 q = 1) : d190291 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188596, d190291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188596, d190291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d188597 q = 1) : d190292 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188597, d190292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d188597, d190292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d188598 q = 1) : d190293 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188598, d190293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d188598, d190293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43949 (p : Pattern) (ha : d102055 p = 1) (hb : d188604 p = 1) : d190299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188599 q = 1) : d190294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188599, d190294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43948 q ha hb
    | true =>
      simp only [d188599, d190294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43813 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188600 q = 1) : d190295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188600, d190295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188600, d190295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188601 q = 1) : d190296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188601, d190296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188601, d190296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188602 q = 1) : d190297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188602, d190297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188602, d190297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188603 q = 1) : d190298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188603, d190298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188603, d190298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188604 q = 1) : d190299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188604, d190299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188604, d190299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43950 (p : Pattern) (ha : d102055 p = 1) (hb : d188610 p = 1) : d190305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188605 q = 1) : d190300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188605, d190300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188605, d190300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43949 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188606 q = 1) : d190301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188606, d190301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188606, d190301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188607 q = 1) : d190302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188607, d190302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188607, d190302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188608 q = 1) : d190303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188608, d190303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188608, d190303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188609 q = 1) : d190304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188609, d190304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188609, d190304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188610 q = 1) : d190305 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188610, d190305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188610, d190305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43951 (p : Pattern) (ha : d102055 p = 1) (hb : d188616 p = 1) : d190311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188611 q = 1) : d190306 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188611, d190306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188611, d190306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43950 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188612 q = 1) : d190307 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188612, d190307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188612, d190307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188613 q = 1) : d190308 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188613, d190308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188613, d190308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188614 q = 1) : d190309 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188614, d190309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188614, d190309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188615 q = 1) : d190310 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188615, d190310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188615, d190310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188616 q = 1) : d190311 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188616, d190311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188616, d190311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43952 (p : Pattern) (ha : d102055 p = 1) (hb : d188621 p = 1) : d190315 p = 1 := by
  have h0 (q : Pattern) (ha : d102054 q = 1) (hb : d188620 q = 1) : d188620 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129568 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188621 q = 1) : d190315 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d102055, d188621, d190315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102055, d188621, d190315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro43953 (p : Pattern) (ha : d102055 p = 1) (hb : d188627 p = 1) : d190321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188622 q = 1) : d190316 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188622, d190316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43952 q ha hb
    | true =>
      simp only [d188622, d190316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188623 q = 1) : d190317 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188623, d190317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188623, d190317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20164 q = 1) (hb : d102055 q = 1) : d190070 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43824 q ha hb
    | true =>
      simp only [d20164, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20165 q = 1) (hb : d102055 q = 1) : d190071 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188624 q = 1) : d190318 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188624, d190318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188624, d190318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188625 q = 1) : d190319 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188625, d190319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188625, d190319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d188626 q = 1) : d190320 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188626, d190320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d188626, d190320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d188627 q = 1) : d190321 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188627, d190321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d188627, d190321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43954 (p : Pattern) (ha : d102055 p = 1) (hb : d188633 p = 1) : d190327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188628 q = 1) : d190322 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188628, d190322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43953 q ha hb
    | true =>
      simp only [d188628, d190322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43825 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188629 q = 1) : d190323 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188629, d190323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188629, d190323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188630 q = 1) : d190324 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188630, d190324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188630, d190324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188631 q = 1) : d190325 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188631, d190325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188631, d190325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188632 q = 1) : d190326 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188632, d190326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188632, d190326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188633 q = 1) : d190327 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188633, d190327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188633, d190327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43955 (p : Pattern) (ha : d102055 p = 1) (hb : d188639 p = 1) : d190333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188634 q = 1) : d190328 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188634, d190328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188634, d190328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43954 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188635 q = 1) : d190329 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188635, d190329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188635, d190329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188636 q = 1) : d190330 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188636, d190330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188636, d190330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188637 q = 1) : d190331 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188637, d190331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188637, d190331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188638 q = 1) : d190332 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188638, d190332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188638, d190332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188639 q = 1) : d190333 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188639, d190333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188639, d190333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43956 (p : Pattern) (ha : d102055 p = 1) (hb : d188645 p = 1) : d190339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188640 q = 1) : d190334 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188640, d190334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188640, d190334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43955 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188641 q = 1) : d190335 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188641, d190335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188641, d190335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188642 q = 1) : d190336 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188642, d190336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188642, d190336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188643 q = 1) : d190337 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188643, d190337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188643, d190337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188644 q = 1) : d190338 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188644, d190338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188644, d190338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188645 q = 1) : d190339 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188645, d190339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188645, d190339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43957 (p : Pattern) (ha : d102055 p = 1) (hb : d188651 p = 1) : d190344 p = 1 := by
  have h0 (q : Pattern) (ha : d102054 q = 1) (hb : d188650 q = 1) : d188650 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188651 q = 1) : d190344 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d102055, d188651, d190344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102055, d188651, d190344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro43958 (p : Pattern) (ha : d102055 p = 1) (hb : d188657 p = 1) : d190350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188652 q = 1) : d190345 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d188652, d190345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43957 q ha hb
    | true =>
      simp only [d188652, d190345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188653 q = 1) : d190346 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d188653, d190346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188653, d190346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20269 q = 1) (hb : d102055 q = 1) : d190129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43836 q ha hb
    | true =>
      simp only [d20269, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20270 q = 1) (hb : d102055 q = 1) : d190130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188654 q = 1) : d190347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d188654, d190347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188654, d190347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188655 q = 1) : d190348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d188655, d190348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188655, d190348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d188656 q = 1) : d190349 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d188656, d190349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d188656, d190349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d188657 q = 1) : d190350 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d188657, d190350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d188657, d190350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43959 (p : Pattern) (ha : d102055 p = 1) (hb : d188663 p = 1) : d190356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188658 q = 1) : d190351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188658, d190351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43958 q ha hb
    | true =>
      simp only [d188658, d190351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43837 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188659 q = 1) : d190352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d188659, d190352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188659, d190352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188660 q = 1) : d190353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d188660, d190353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188660, d190353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188661 q = 1) : d190354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d188661, d190354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188661, d190354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188662 q = 1) : d190355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d188662, d190355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188662, d190355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188663 q = 1) : d190356 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d188663, d190356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188663, d190356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43960 (p : Pattern) (ha : d102055 p = 1) (hb : d188669 p = 1) : d190362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188664 q = 1) : d190357 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d188664, d190357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188664, d190357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43959 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188665 q = 1) : d190358 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d188665, d190358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188665, d190358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188666 q = 1) : d190359 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d188666, d190359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188666, d190359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188667 q = 1) : d190360 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d188667, d190360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188667, d190360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188668 q = 1) : d190361 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d188668, d190361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188668, d190361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188669 q = 1) : d190362 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d188669, d190362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188669, d190362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43961 (p : Pattern) (ha : d102055 p = 1) (hb : d188675 p = 1) : d190368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188670 q = 1) : d190363 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d188670, d190363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188670, d190363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43960 q ha hb
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188671 q = 1) : d190364 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d188671, d190364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188671, d190364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188672 q = 1) : d190365 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d188672, d190365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188672, d190365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188673 q = 1) : d190366 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d188673, d190366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188673, d190366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188674 q = 1) : d190367 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d188674, d190367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188674, d190367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188675 q = 1) : d190368 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d188675, d190368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d188675, d190368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43962 (p : Pattern) (ha : d102055 p = 1) (hb : d188681 p = 1) : d190374 p = 1 := by
  have h0 (q : Pattern) (ha : d102055 q = 1) (hb : d188570 q = 1) : d190266 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188570, d190266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43940 q ha hb
    | true =>
      simp only [d188570, d190266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43943 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188589 q = 1) : d190285 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188589, d190285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188589, d190285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43946 q ha hb
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188590 q = 1) : d190286 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d188590, d190286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d188590, d190286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188617 q = 1) : d190312 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188617, d190312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188617, d190312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43951 q ha hb
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188618 q = 1) : d190313 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d188618, d190313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188618, d190313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188619 q = 1) : d190314 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d188619, d190314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188619, d190314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102055 q = 1) (hb : d188646 q = 1) : d190340 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188646, d190340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188646, d190340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43956 q ha hb
  have h8 (q : Pattern) (ha : d102055 q = 1) (hb : d188647 q = 1) : d190341 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d188647, d190341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188647, d190341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d102055 q = 1) (hb : d188648 q = 1) : d190342 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d188648, d190342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188648, d190342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d102055 q = 1) (hb : d188649 q = 1) : d190343 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d188649, d190343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d188649, d190343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102055 q = 1) (hb : d188676 q = 1) : d190369 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d188676, d190369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188676, d190369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43961 q ha hb
  have h12 (q : Pattern) (ha : d102055 q = 1) (hb : d188677 q = 1) : d190370 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d188677, d190370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188677, d190370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102055 q = 1) (hb : d188678 q = 1) : d190371 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d188678, d190371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188678, d190371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102055 q = 1) (hb : d188679 q = 1) : d190372 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d188679, d190372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d188679, d190372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102055 q = 1) (hb : d188680 q = 1) : d190373 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d188680, d190373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d188680, d190373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102055 q = 1) (hb : d188681 q = 1) : d190374 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d188681, d190374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d188681, d190374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43963 (p : Pattern) (ha : d102055 p = 1) (hb : d188687 p = 1) : d190380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188682 q = 1) : d190375 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d188682, d190375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43962 q ha hb
    | true =>
      simp only [d188682, d190375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188683 q = 1) : d190376 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d188683, d190376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188683, d190376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188684 q = 1) : d190377 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d188684, d190377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188684, d190377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188685 q = 1) : d190378 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d188685, d190378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188685, d190378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188686 q = 1) : d190379 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d188686, d190379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188686, d190379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188687 q = 1) : d190380 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d188687, d190380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188687, d190380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43964 (p : Pattern) (ha : d102055 p = 1) (hb : d188693 p = 1) : d190386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188688 q = 1) : d190381 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d188688, d190381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43963 q ha hb
    | true =>
      simp only [d188688, d190381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188689 q = 1) : d190382 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d188689, d190382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188689, d190382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188690 q = 1) : d190383 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d188690, d190383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188690, d190383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188691 q = 1) : d190384 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d188691, d190384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188691, d190384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188692 q = 1) : d190385 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d188692, d190385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188692, d190385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188693 q = 1) : d190386 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d188693, d190386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188693, d190386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43965 (p : Pattern) (ha : d102055 p = 1) (hb : d188699 p = 1) : d190392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188694 q = 1) : d190387 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d188694, d190387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43964 q ha hb
    | true =>
      simp only [d188694, d190387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188695 q = 1) : d190388 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d188695, d190388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188695, d190388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188696 q = 1) : d190389 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d188696, d190389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188696, d190389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188697 q = 1) : d190390 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d188697, d190390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188697, d190390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188698 q = 1) : d190391 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d188698, d190391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188698, d190391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188699 q = 1) : d190392 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d188699, d190392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188699, d190392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43966 (p : Pattern) (ha : d102055 p = 1) (hb : d188705 p = 1) : d190398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188700 q = 1) : d190393 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d188700, d190393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43965 q ha hb
    | true =>
      simp only [d188700, d190393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188701 q = 1) : d190394 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d188701, d190394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188701, d190394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188702 q = 1) : d190395 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d188702, d190395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188702, d190395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188703 q = 1) : d190396 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d188703, d190396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188703, d190396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188704 q = 1) : d190397 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d188704, d190397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188704, d190397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188705 q = 1) : d190398 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d188705, d190398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188705, d190398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43967 (p : Pattern) (ha : d102055 p = 1) (hb : d188711 p = 1) : d190404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188706 q = 1) : d190399 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d188706, d190399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43966 q ha hb
    | true =>
      simp only [d188706, d190399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188707 q = 1) : d190400 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d188707, d190400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188707, d190400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188708 q = 1) : d190401 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d188708, d190401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188708, d190401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188709 q = 1) : d190402 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d188709, d190402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188709, d190402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188710 q = 1) : d190403 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d188710, d190403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188710, d190403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188711 q = 1) : d190404 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d188711, d190404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188711, d190404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43968 (p : Pattern) (ha : d102055 p = 1) (hb : d188717 p = 1) : d190410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188712 q = 1) : d190405 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d188712, d190405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43967 q ha hb
    | true =>
      simp only [d188712, d190405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188713 q = 1) : d190406 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d188713, d190406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188713, d190406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188714 q = 1) : d190407 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d188714, d190407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188714, d190407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188715 q = 1) : d190408 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d188715, d190408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188715, d190408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188716 q = 1) : d190409 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d188716, d190409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188716, d190409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188717 q = 1) : d190410 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d188717, d190410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188717, d190410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43969 (p : Pattern) (ha : d102055 p = 1) (hb : d188723 p = 1) : d190416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102055 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102055 q = 1) (hb : d188718 q = 1) : d190411 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d188718, d190411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43968 q ha hb
    | true =>
      simp only [d188718, d190411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102055 q = 1) (hb : d188719 q = 1) : d190412 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d188719, d190412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188719, d190412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102055 q = 1) (hb : d188720 q = 1) : d190413 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d188720, d190413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188720, d190413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102055 q = 1) (hb : d188721 q = 1) : d190414 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d188721, d190414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188721, d190414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102055 q = 1) (hb : d188722 q = 1) : d190415 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d188722, d190415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188722, d190415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102055 q = 1) (hb : d188723 q = 1) : d190416 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d188723, d190416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188723, d190416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43970 (p : Pattern) (ha : d189362 p = 1) (hb : d189881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189357 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189332 q = 1) (hb : d189817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189332, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43857 q ha hb
    | true =>
      simp only [d189332, d189817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189358 q = 1) (hb : d189877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189358, d189877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189358, d189877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189333 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d189359 q = 1) (hb : d189878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189359, d189878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189359, d189878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d189360 q = 1) (hb : d189879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189360, d189879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189360, d189879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189361 q = 1) (hb : d189880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189361, d189880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189361, d189880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189362 q = 1) (hb : d189881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189362, d189881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189362, d189881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43971 (p : Pattern) (ha : d189368 p = 1) (hb : d190225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189363 q = 1) (hb : d189882 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189363, d189882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189363, d189882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43970 q ha hb
  have h2 (q : Pattern) (ha : d189364 q = 1) (hb : d190221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189364, d190221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189364, d190221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189365 q = 1) (hb : d190222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189365, d190222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189365, d190222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189366 q = 1) (hb : d190223 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189366, d190223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189366, d190223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189367 q = 1) (hb : d190224 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189367, d190224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189367, d190224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189368 q = 1) (hb : d190225 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189368, d190225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189368, d190225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43972 (p : Pattern) (ha : d189394 p = 1) (hb : d190235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189383 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189357 q = 1) (hb : d189840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189357, d189840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43861 q ha hb
    | true =>
      simp only [d189357, d189840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43857 q ha hb
  have h3 (q : Pattern) (ha : d189384 q = 1) (hb : d190231 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189384, d190231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189384, d190231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189390 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d189391 q = 1) (hb : d190232 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189391, d190232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189391, d190232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d189392 q = 1) (hb : d190233 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189392, d190233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189392, d190233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189393 q = 1) (hb : d190234 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189393, d190234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189393, d190234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189394 q = 1) (hb : d190235 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189394, d190235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189394, d190235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43973 (p : Pattern) (ha : d189406 p = 1) (hb : d190241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189395 q = 1) (hb : d190236 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189395, d190236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189395, d190236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43972 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189402 q = 1) (hb : d190237 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189402, d190237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189402, d190237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189403 q = 1) (hb : d190238 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189403, d190238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189403, d190238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189404 q = 1) (hb : d190239 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189404, d190239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189404, d190239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189405 q = 1) (hb : d190240 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189405, d190240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189405, d190240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189406 q = 1) (hb : d190241 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189406, d190241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189406, d190241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43974 (p : Pattern) (ha : d189412 p = 1) (hb : d190247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d189347 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189369 q = 1) (hb : d190226 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189369, d190226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189369, d190226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43971 q ha hb
  have h3 (q : Pattern) (ha : d189370 q = 1) (hb : d190227 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189370, d190227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189370, d190227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189371 q = 1) (hb : d190228 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189371, d190228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189371, d190228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189372 q = 1) (hb : d190229 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189372, d190229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189372, d190229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189373 q = 1) (hb : d190230 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189373, d190230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189373, d190230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189407 q = 1) (hb : d190242 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189407, d190242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189407, d190242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43973 q ha hb
  have h8 (q : Pattern) (ha : d189408 q = 1) (hb : d190243 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189408, d190243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189408, d190243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189409 q = 1) (hb : d190244 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189409, d190244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189409, d190244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d189410 q = 1) (hb : d190245 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189410, d190245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189410, d190245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d189411 q = 1) (hb : d190246 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189411, d190246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189411, d190246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d189412 q = 1) (hb : d190247 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189412, d190247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189412, d190247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro43975 (p : Pattern) (ha : d189450 p = 1) (hb : d190253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189434 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189439 q = 1) (hb : d190248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189439, d190248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43875 q ha hb
    | true =>
      simp only [d189439, d190248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43878 q ha hb
  have h3 (q : Pattern) (ha : d189440 q = 1) (hb : d190249 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189440, d190249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189440, d190249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189446 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d189447 q = 1) (hb : d190250 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189447, d190250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189447, d190250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d189448 q = 1) (hb : d190251 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189448, d190251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189448, d190251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189449 q = 1) (hb : d190252 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189449, d190252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189449, d190252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189450 q = 1) (hb : d190253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189450, d190253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189450, d190253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43976 (p : Pattern) (ha : d189463 p = 1) (hb : d190259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189451 q = 1) (hb : d190254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189451, d190254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189451, d190254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43975 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189458 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189459 q = 1) (hb : d190255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189459, d190255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189459, d190255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189460 q = 1) (hb : d190256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189460, d190256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189460, d190256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189461 q = 1) (hb : d190257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189461, d190257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189461, d190257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189462 q = 1) (hb : d190258 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189462, d190258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189462, d190258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189463 q = 1) (hb : d190259 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189463, d190259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189463, d190259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43977 (p : Pattern) (ha : d189469 p = 1) (hb : d190265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189464 q = 1) (hb : d190260 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189464, d190260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189464, d190260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43976 q ha hb
  have h2 (q : Pattern) (ha : d189465 q = 1) (hb : d190261 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189465, d190261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189465, d190261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189466 q = 1) (hb : d190262 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189466, d190262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189466, d190262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189467 q = 1) (hb : d190263 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189467, d190263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189467, d190263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189468 q = 1) (hb : d190264 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189468, d190264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189468, d190264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189469 q = 1) (hb : d190265 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189469, d190265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189469, d190265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43978 (p : Pattern) (ha : d189511 p = 1) (hb : d190272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189500 q = 1) (hb : d190267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189500, d190267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43886 q ha hb
    | true =>
      simp only [d189500, d190267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43889 q ha hb
  have h3 (q : Pattern) (ha : d189501 q = 1) (hb : d190268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189501, d190268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189501, d190268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189507 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d189508 q = 1) (hb : d190269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189508, d190269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189508, d190269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d189509 q = 1) (hb : d190270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189509, d190270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189509, d190270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189510 q = 1) (hb : d190271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189510, d190271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189510, d190271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189511 q = 1) (hb : d190272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189511, d190272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189511, d190272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43979 (p : Pattern) (ha : d189524 p = 1) (hb : d190278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189512 q = 1) (hb : d190273 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189512, d190273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189512, d190273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43978 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189519 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189520 q = 1) (hb : d190274 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189520, d190274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189520, d190274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189521 q = 1) (hb : d190275 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189521, d190275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189521, d190275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189522 q = 1) (hb : d190276 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189522, d190276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189522, d190276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189523 q = 1) (hb : d190277 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189523, d190277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189523, d190277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189524 q = 1) (hb : d190278 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189524, d190278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189524, d190278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43980 (p : Pattern) (ha : d189530 p = 1) (hb : d190284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189525 q = 1) (hb : d190279 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189525, d190279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189525, d190279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43979 q ha hb
  have h2 (q : Pattern) (ha : d189526 q = 1) (hb : d190280 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189526, d190280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189526, d190280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189527 q = 1) (hb : d190281 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189527, d190281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189527, d190281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189528 q = 1) (hb : d190282 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189528, d190282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189528, d190282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189529 q = 1) (hb : d190283 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189529, d190283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189529, d190283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189530 q = 1) (hb : d190284 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189530, d190284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189530, d190284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43981 (p : Pattern) (ha : d189560 p = 1) (hb : d190287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h3 (q : Pattern) (ha : d20037 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20038 q = 1) (hb : d189536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d189536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d189536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h7 (q : Pattern) (ha : d20039 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20040 q = 1) (hb : d189537 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d189537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d189537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20041 q = 1) (hb : d189538 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d189538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20041, d189538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h12 (q : Pattern) (ha : d20055 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20056 q = 1) (hb : d189550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, d189550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, d189550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20057 q = 1) (hb : d189551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, d189551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20057, d189551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d188591 q = 1) (hb : d189560 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188591, d189560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d188591, d189560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d189560 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d189560 q = 1) (hb : d190287 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d190287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro43982 (p : Pattern) (ha : d189566 p = 1) (hb : d190293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189561 q = 1) (hb : d190288 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189561, d190288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43981 q ha hb
    | true =>
      simp only [d189561, d190288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189562 q = 1) (hb : d190289 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189562, d190289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189562, d190289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189553 q = 1) (hb : d190012 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189553, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43896 q ha hb
    | true =>
      simp only [d189553, d190012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189554 q = 1) (hb : d190013 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189554, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189554, d190013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189563 q = 1) (hb : d190290 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189563, d190290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189563, d190290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189564 q = 1) (hb : d190291 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189564, d190291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189564, d190291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189565 q = 1) (hb : d190292 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189565, d190292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189565, d190292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189566 q = 1) (hb : d190293 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189566, d190293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189566, d190293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43983 (p : Pattern) (ha : d189587 p = 1) (hb : d190299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189559 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189571 q = 1) (hb : d190294 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189571, d190294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43982 q ha hb
    | true =>
      simp only [d189571, d190294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43901 q ha hb
  have h3 (q : Pattern) (ha : d189572 q = 1) (hb : d190295 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189572, d190295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189572, d190295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189583 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d189584 q = 1) (hb : d190296 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189584, d190296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189584, d190296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d189585 q = 1) (hb : d190297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189585, d190297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189585, d190297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189586 q = 1) (hb : d190298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189586, d190298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189586, d190298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189587 q = 1) (hb : d190299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189587, d190299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189587, d190299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43984 (p : Pattern) (ha : d189600 p = 1) (hb : d190305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189588 q = 1) (hb : d190300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189588, d190300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189588, d190300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43983 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189595 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189596 q = 1) (hb : d190301 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189596, d190301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189596, d190301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189597 q = 1) (hb : d190302 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189597, d190302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189597, d190302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189598 q = 1) (hb : d190303 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189598, d190303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189598, d190303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189599 q = 1) (hb : d190304 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189599, d190304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189599, d190304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189600 q = 1) (hb : d190305 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189600, d190305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189600, d190305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43985 (p : Pattern) (ha : d189606 p = 1) (hb : d190311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189601 q = 1) (hb : d190306 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189601, d190306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189601, d190306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43984 q ha hb
  have h2 (q : Pattern) (ha : d189602 q = 1) (hb : d190307 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189602, d190307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189602, d190307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189603 q = 1) (hb : d190308 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189603, d190308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189603, d190308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189604 q = 1) (hb : d190309 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189604, d190309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189604, d190309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189605 q = 1) (hb : d190310 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189605, d190310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189605, d190310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189606 q = 1) (hb : d190311 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189606, d190311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189606, d190311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43986 (p : Pattern) (ha : d189637 p = 1) (hb : d190315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h3 (q : Pattern) (ha : d20141 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20142 q = 1) (hb : d189613 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d189613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d189613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h7 (q : Pattern) (ha : d20143 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20144 q = 1) (hb : d189614 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d189614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d189614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20145 q = 1) (hb : d189615 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d189615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20145, d189615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h12 (q : Pattern) (ha : d20159 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20160 q = 1) (hb : d189627 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, d189627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20160, d189627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20161 q = 1) (hb : d189628 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, d189628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20161, d189628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d188620 q = 1) (hb : d189637 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188620, d189637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d188620, d189637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d189637 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d189637 q = 1) (hb : d190315 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d190315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro43987 (p : Pattern) (ha : d189643 p = 1) (hb : d190321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189638 q = 1) (hb : d190316 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189638, d190316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43986 q ha hb
    | true =>
      simp only [d189638, d190316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189639 q = 1) (hb : d190317 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189639, d190317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189639, d190317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189630 q = 1) (hb : d190070 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189630, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43908 q ha hb
    | true =>
      simp only [d189630, d190070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189631 q = 1) (hb : d190071 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189631, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189631, d190071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189640 q = 1) (hb : d190318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189640, d190318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189640, d190318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189641 q = 1) (hb : d190319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189641, d190319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189641, d190319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189642 q = 1) (hb : d190320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189642, d190320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189642, d190320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189643 q = 1) (hb : d190321 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189643, d190321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189643, d190321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43988 (p : Pattern) (ha : d189664 p = 1) (hb : d190327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189636 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189648 q = 1) (hb : d190322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189648, d190322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43987 q ha hb
    | true =>
      simp only [d189648, d190322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43913 q ha hb
  have h3 (q : Pattern) (ha : d189649 q = 1) (hb : d190323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189649, d190323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189649, d190323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189660 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d189661 q = 1) (hb : d190324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189661, d190324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189661, d190324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d189662 q = 1) (hb : d190325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189662, d190325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189662, d190325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189663 q = 1) (hb : d190326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189663, d190326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189663, d190326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189664 q = 1) (hb : d190327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189664, d190327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189664, d190327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43989 (p : Pattern) (ha : d189677 p = 1) (hb : d190333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189665 q = 1) (hb : d190328 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189665, d190328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189665, d190328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43988 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189673 q = 1) (hb : d190329 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189673, d190329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189673, d190329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189674 q = 1) (hb : d190330 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189674, d190330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189674, d190330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189675 q = 1) (hb : d190331 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189675, d190331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189675, d190331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189676 q = 1) (hb : d190332 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189676, d190332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189676, d190332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189677 q = 1) (hb : d190333 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189677, d190333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189677, d190333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43990 (p : Pattern) (ha : d189683 p = 1) (hb : d190339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189678 q = 1) (hb : d190334 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189678, d190334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189678, d190334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43989 q ha hb
  have h2 (q : Pattern) (ha : d189679 q = 1) (hb : d190335 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189679, d190335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189679, d190335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189680 q = 1) (hb : d190336 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189680, d190336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189680, d190336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189681 q = 1) (hb : d190337 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189681, d190337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189681, d190337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189682 q = 1) (hb : d190338 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189682, d190338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189682, d190338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189683 q = 1) (hb : d190339 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189683, d190339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189683, d190339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43991 (p : Pattern) (ha : d189715 p = 1) (hb : d190344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h3 (q : Pattern) (ha : d20246 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20247 q = 1) (hb : d189691 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d189691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d189691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h7 (q : Pattern) (ha : d20248 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20249 q = 1) (hb : d189692 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d189692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d189692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20250 q = 1) (hb : d189693 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d189693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20250, d189693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h12 (q : Pattern) (ha : d20264 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20265 q = 1) (hb : d189705 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, d189705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20265, d189705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20266 q = 1) (hb : d189706 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, d189706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20266, d189706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d188650 q = 1) (hb : d189715 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d188650, d189715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d188650, d189715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d189715 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d189715 q = 1) (hb : d190344 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d190344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d190344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro43992 (p : Pattern) (ha : d189721 p = 1) (hb : d190350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189716 q = 1) (hb : d190345 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189716, d190345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43991 q ha hb
    | true =>
      simp only [d189716, d190345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189717 q = 1) (hb : d190346 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189717, d190346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189717, d190346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189708 q = 1) (hb : d190129 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d189708, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43920 q ha hb
    | true =>
      simp only [d189708, d190129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189709 q = 1) (hb : d190130 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d189709, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189709, d190130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189718 q = 1) (hb : d190347 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d189718, d190347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189718, d190347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189719 q = 1) (hb : d190348 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d189719, d190348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189719, d190348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189720 q = 1) (hb : d190349 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d189720, d190349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189720, d190349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d189721 q = 1) (hb : d190350 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d189721, d190350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d189721, d190350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro43993 (p : Pattern) (ha : d189742 p = 1) (hb : d190356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d189714 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189726 q = 1) (hb : d190351 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d189726, d190351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43992 q ha hb
    | true =>
      simp only [d189726, d190351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43925 q ha hb
  have h3 (q : Pattern) (ha : d189727 q = 1) (hb : d190352 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189727, d190352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189727, d190352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d189738 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d189739 q = 1) (hb : d190353 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d189739, d190353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189739, d190353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d189740 q = 1) (hb : d190354 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d189740, d190354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189740, d190354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189741 q = 1) (hb : d190355 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d189741, d190355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189741, d190355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d189742 q = 1) (hb : d190356 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d189742, d190356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189742, d190356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro43994 (p : Pattern) (ha : d189755 p = 1) (hb : d190362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189743 q = 1) (hb : d190357 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d189743, d190357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189743, d190357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43993 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d189750 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d189751 q = 1) (hb : d190358 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d189751, d190358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189751, d190358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d189752 q = 1) (hb : d190359 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d189752, d190359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189752, d190359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189753 q = 1) (hb : d190360 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d189753, d190360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189753, d190360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189754 q = 1) (hb : d190361 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d189754, d190361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189754, d190361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d189755 q = 1) (hb : d190362 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d189755, d190362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189755, d190362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro43995 (p : Pattern) (ha : d189761 p = 1) (hb : d190368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189756 q = 1) (hb : d190363 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d189756, d190363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189756, d190363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43994 q ha hb
  have h2 (q : Pattern) (ha : d189757 q = 1) (hb : d190364 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d189757, d190364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189757, d190364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d189758 q = 1) (hb : d190365 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d189758, d190365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189758, d190365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189759 q = 1) (hb : d190366 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d189759, d190366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189759, d190366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d189760 q = 1) (hb : d190367 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d189760, d190367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189760, d190367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189761 q = 1) (hb : d190368 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d189761, d190368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d189761, d190368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro43996 (p : Pattern) (ha : d189767 p = 1) (hb : d190374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d189470 q = 1) (hb : d190266 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189470, d190266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43974 q ha hb
    | true =>
      simp only [d189470, d190266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43977 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d189531 q = 1) (hb : d190285 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189531, d190285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189531, d190285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43980 q ha hb
  have h3 (q : Pattern) (ha : d189532 q = 1) (hb : d190286 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189532, d190286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d189532, d190286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d189607 q = 1) (hb : d190312 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189607, d190312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189607, d190312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43985 q ha hb
  have h5 (q : Pattern) (ha : d189608 q = 1) (hb : d190313 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189608, d190313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189608, d190313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d189609 q = 1) (hb : d190314 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189609, d190314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189609, d190314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d189684 q = 1) (hb : d190340 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189684, d190340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189684, d190340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43990 q ha hb
  have h8 (q : Pattern) (ha : d189685 q = 1) (hb : d190341 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189685, d190341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189685, d190341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d189686 q = 1) (hb : d190342 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189686, d190342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189686, d190342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d189687 q = 1) (hb : d190343 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d189687, d190343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d189687, d190343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d189762 q = 1) (hb : d190369 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d189762, d190369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189762, d190369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43995 q ha hb
  have h12 (q : Pattern) (ha : d189763 q = 1) (hb : d190370 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d189763, d190370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189763, d190370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d189764 q = 1) (hb : d190371 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d189764, d190371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189764, d190371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d189765 q = 1) (hb : d190372 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d189765, d190372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d189765, d190372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d189766 q = 1) (hb : d190373 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d189766, d190373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d189766, d190373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d189767 q = 1) (hb : d190374 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d189767, d190374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d189767, d190374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro43997 (p : Pattern) (ha : d189773 p = 1) (hb : d190380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189768 q = 1) (hb : d190375 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d189768, d190375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43996 q ha hb
    | true =>
      simp only [d189768, d190375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189769 q = 1) (hb : d190376 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d189769, d190376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189769, d190376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189770 q = 1) (hb : d190377 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d189770, d190377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189770, d190377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189771 q = 1) (hb : d190378 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d189771, d190378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189771, d190378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189772 q = 1) (hb : d190379 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d189772, d190379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189772, d190379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189773 q = 1) (hb : d190380 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d189773, d190380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189773, d190380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43998 (p : Pattern) (ha : d189779 p = 1) (hb : d190386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189774 q = 1) (hb : d190381 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d189774, d190381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43997 q ha hb
    | true =>
      simp only [d189774, d190381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189775 q = 1) (hb : d190382 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d189775, d190382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189775, d190382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189776 q = 1) (hb : d190383 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d189776, d190383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189776, d190383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189777 q = 1) (hb : d190384 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d189777, d190384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189777, d190384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189778 q = 1) (hb : d190385 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d189778, d190385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189778, d190385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189779 q = 1) (hb : d190386 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d189779, d190386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189779, d190386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro43999 (p : Pattern) (ha : d189785 p = 1) (hb : d190392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d189780 q = 1) (hb : d190387 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d189780, d190387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43998 q ha hb
    | true =>
      simp only [d189780, d190387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d189781 q = 1) (hb : d190388 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d189781, d190388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d189781, d190388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d189782 q = 1) (hb : d190389 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d189782, d190389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d189782, d190389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d189783 q = 1) (hb : d190390 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d189783, d190390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d189783, d190390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d189784 q = 1) (hb : d190391 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d189784, d190391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d189784, d190391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d189785 q = 1) (hb : d190392 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d189785, d190392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d189785, d190392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
